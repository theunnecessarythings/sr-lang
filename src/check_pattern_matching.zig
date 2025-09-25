const Checker = @import("checker.zig").Checker;
const std = @import("std");
const ast = @import("ast.zig");
const types = @import("types.zig");
const symbols = @import("symbols.zig");
const check_types = @import("check_types.zig");

pub fn checkPattern(
    self: *Checker,
    pid: ast.PatternId,
    value_ty: types.TypeId,
    top_level: bool,
) !bool {
    const emit = top_level;
    const k = self.ast_unit.pats.index.kinds.items[pid.toRaw()];

    switch (k) {
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
            // Bind the name to the value (capture)
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
            // For now: allow only integer-typed subjects; assume range matches
            const knd = self.type_info.store.index.kinds.items[value_ty.toRaw()];
            const is_int = switch (knd) {
                .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize => true,
                else => false,
            };
            return is_int;
        },
        .VariantTuple => {
            const vt_pat = self.ast_unit.pats.get(.VariantTuple, pid);
            const value_kind = self.type_info.store.index.kinds.items[value_ty.toRaw()];
            if (value_kind != .Variant and value_kind != .Error) return false;
            const cases = if (value_kind == .Variant)
                self.type_info.store.field_pool.slice(self.type_info.store.Variant.get(self.type_info.store.index.rows.items[value_ty.toRaw()]).variants)
            else
                self.type_info.store.field_pool.slice(self.type_info.store.Error.get(self.type_info.store.index.rows.items[value_ty.toRaw()]).variants);
            const segs = self.ast_unit.pats.seg_pool.slice(vt_pat.path);
            if (segs.len == 0) return false;
            const last = self.ast_unit.pats.PathSeg.get(segs[segs.len - 1].toRaw());
            var payload_ty: ?types.TypeId = null;
            for (cases) |fid| {
                const f = self.type_info.store.Field.get(fid.toRaw());
                if (f.name.toRaw() == last.name.toRaw()) {
                    payload_ty = f.ty;
                    break;
                }
            }
            if (payload_ty == null) return false;
            const pk = self.type_info.store.index.kinds.items[payload_ty.?.toRaw()];
            const elems = self.ast_unit.pats.pat_pool.slice(vt_pat.elems);
            if (pk == .Void) {
                // No payload expected
                return elems.len == 0;
            }
            if (pk != .Tuple) return false;
            const tup = self.type_info.store.Tuple.get(self.type_info.store.index.rows.items[payload_ty.?.toRaw()]);
            const tys = self.type_info.store.type_pool.slice(tup.elems);
            if (elems.len != tys.len) return false;
            for (elems, 0..) |eid, i| {
                if (!(try checkPattern(self, eid, tys[i], false))) return false;
            }
            return true;
        },
        .Path => {
            // Handle enum tags and variant/error tag-only patterns (no payload)
            const pp = self.ast_unit.pats.get(.Path, pid);
            const segs = self.ast_unit.pats.seg_pool.slice(pp.segments);
            if (segs.len == 0) return false;
            const last = self.ast_unit.pats.PathSeg.get(segs[segs.len - 1].toRaw());
            const vk = self.type_info.store.index.kinds.items[value_ty.toRaw()];
            switch (vk) {
                .Enum => {
                    const er = self.type_info.store.Enum.get(self.type_info.store.index.rows.items[value_ty.toRaw()]);
                    const members = self.type_info.store.enum_member_pool.slice(er.members);
                    for (members) |mid| {
                        const m = self.type_info.store.EnumMember.get(mid.toRaw());
                        if (m.name.toRaw() == last.name.toRaw()) return true;
                    }
                    return false;
                },
                .Variant, .Error => {
                    const cases = if (vk == .Variant)
                        self.type_info.store.field_pool.slice(self.type_info.store.Variant.get(self.type_info.store.index.rows.items[value_ty.toRaw()]).variants)
                    else
                        self.type_info.store.field_pool.slice(self.type_info.store.Error.get(self.type_info.store.index.rows.items[value_ty.toRaw()]).variants);
                    for (cases) |fid| {
                        const f = self.type_info.store.Field.get(fid.toRaw());
                        if (f.name.toRaw() == last.name.toRaw()) {
                            const ft_k = self.type_info.store.index.kinds.items[f.ty.toRaw()];
                            return ft_k == .Void; // tag-only allowed only when payload is void
                        }
                    }
                    return false;
                },
                else => return false,
            }
        },
        .VariantStruct => {
            const vs_pat = self.ast_unit.pats.get(.VariantStruct, pid);
            const value_kind = self.type_info.store.index.kinds.items[value_ty.toRaw()];
            if (value_kind != .Variant and value_kind != .Error) {
                // If the subject is a struct, treat VariantStruct pattern like a Struct pattern (path as type name)
                if (value_kind == .Struct) {
                    const st = self.type_info.store.Struct.get(self.type_info.store.index.rows.items[value_ty.toRaw()]);
                    const value_fields = self.type_info.store.field_pool.slice(st.fields);
                    const pat_fields = self.ast_unit.pats.field_pool.slice(vs_pat.fields);
                    for (pat_fields) |pfid| {
                        const pf = self.ast_unit.pats.StructField.get(pfid.toRaw());
                        var found: bool = false;
                        for (value_fields) |vfid| {
                            const vf = self.type_info.store.Field.get(vfid.toRaw());
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
            const cases = if (value_kind == .Variant)
                self.type_info.store.field_pool.slice(self.type_info.store.Variant.get(self.type_info.store.index.rows.items[value_ty.toRaw()]).variants)
            else
                self.type_info.store.field_pool.slice(self.type_info.store.Error.get(self.type_info.store.index.rows.items[value_ty.toRaw()]).variants);
            const segs = self.ast_unit.pats.seg_pool.slice(vs_pat.path);
            if (segs.len == 0) return false;
            const last = self.ast_unit.pats.PathSeg.get(segs[segs.len - 1].toRaw());
            var payload_ty: ?types.TypeId = null;
            for (cases) |fid| {
                const f = self.type_info.store.Field.get(fid.toRaw());
                if (f.name.toRaw() == last.name.toRaw()) {
                    payload_ty = f.ty;
                    break;
                }
            }
            if (payload_ty == null) return false;
            const pk = self.type_info.store.index.kinds.items[payload_ty.?.toRaw()];
            if (pk == .Void) return vs_pat.fields.len == 0;
            if (pk != .Struct) return false;
            const st = self.type_info.store.Struct.get(self.type_info.store.index.rows.items[payload_ty.?.toRaw()]);
            const value_fields = self.type_info.store.field_pool.slice(st.fields);
            const pat_fields = self.ast_unit.pats.field_pool.slice(vs_pat.fields);
            for (pat_fields) |pfid| {
                const pf = self.ast_unit.pats.StructField.get(pfid.toRaw());
                var found: ?types.TypeId = null;
                for (value_fields) |vfid| {
                    const vf = self.type_info.store.Field.get(vfid.toRaw());
                    if (vf.name.toRaw() == pf.name.toRaw()) {
                        found = vf.ty;
                        break;
                    }
                }
                if (found == null) return false;
                if (!(try checkPattern(self, pf.pattern, found.?, false))) return false;
            }
            return true;
        },
        .Binding => {
            const bp = self.ast_unit.pats.get(.Binding, pid);
            // Declare the bound name in the symbol table
            _ = try self.symtab.declare(.{
                .name = bp.name,
                .kind = .Var, // Or appropriate kind
                .loc = bp.loc,
                .origin_decl = ast.OptDeclId.none(),
                .origin_param = ast.OptParamId.none(),
            });
            // If there's a sub-pattern, check it recursively
            // if (!bp.pattern.isNone()) {
            //     return self.checkPattern(bp.pattern.unwrap(), value_ty, top_level);
            // }
            return true;
        },
        .Wildcard => return true,
        .Literal => {
            const lp = self.ast_unit.pats.get(.Literal, pid);
            const pattern_loc = self.ast_unit.exprs.locs.get(lp.loc);
            const lit_expr_id = lp.expr;
            const lit_ty = (try self.checkExpr(lit_expr_id)) orelse return false;
            if (self.assignable(value_ty, lit_ty) != .success) {
                try self.diags.addError(pattern_loc, .pattern_type_mismatch, .{});
                return false;
            }
            // TODO: For literal patterns, if not top_level, we might need to check the actual value for equality.
            // This would involve evaluating the literal expression and comparing it with the value being matched.
            // For now, only type compatibility is checked.
            return true;
        },
        .Tuple => {
            const tp = self.ast_unit.pats.get(.Tuple, pid);
            const pattern_loc = self.ast_unit.exprs.locs.get(tp.loc);
            const value_kind = self.type_info.store.index.kinds.items[value_ty.toRaw()];
            if (value_kind != .Tuple) {
                if (emit) try self.diags.addError(pattern_loc, .pattern_shape_mismatch, .{});
                return false;
            }
            const value_tuple_ty = self.type_info.store.Tuple.get(self.type_info.store.index.rows.items[value_ty.toRaw()]);
            const pattern_elems = self.ast_unit.pats.pat_pool.slice(tp.elems);
            const value_elems = self.type_info.store.type_pool.slice(value_tuple_ty.elems);

            if (pattern_elems.len != value_elems.len) {
                if (emit) try self.diags.addError(pattern_loc, .tuple_arity_mismatch, .{});
                return false;
            }

            for (pattern_elems, 0..) |pat_elem_id, i| {
                if (!(try checkPattern(self, pat_elem_id, value_elems[i], false))) {
                    return false;
                }
            }
            return true;
        },
        .Slice => {
            const ap = self.ast_unit.pats.get(.Slice, pid);
            const pattern_loc = self.ast_unit.exprs.locs.get(ap.loc);
            const value_kind = self.type_info.store.index.kinds.items[value_ty.toRaw()];
            if (value_kind != .Array and value_kind != .Slice and value_kind != .DynArray) {
                if (emit) try self.diags.addError(pattern_loc, .pattern_type_mismatch, .{});
                return false;
            }
            const elem_ty: types.TypeId = switch (value_kind) {
                .Array => self.type_info.store.Array.get(self.type_info.store.index.rows.items[value_ty.toRaw()]).elem,
                .Slice => self.type_info.store.Slice.get(self.type_info.store.index.rows.items[value_ty.toRaw()]).elem,
                .DynArray => self.type_info.store.DynArray.get(self.type_info.store.index.rows.items[value_ty.toRaw()]).elem,
                else => unreachable,
            };
            const pattern_elems = self.ast_unit.pats.pat_pool.slice(ap.elems);
            if (value_kind == .Array) {
                const arr = self.type_info.store.Array.get(self.type_info.store.index.rows.items[value_ty.toRaw()]);
                if (ap.has_rest) {
                    if (pattern_elems.len > arr.len) return false;
                } else {
                    if (pattern_elems.len != arr.len) return false;
                }
            }
            for (pattern_elems, 0..) |pat_elem_id, i| {
                if (ap.has_rest and i == ap.rest_index) {
                    // Rest placeholder: optionally a binding, which is validated below
                    continue;
                }
                if (!(try checkPattern(self, pat_elem_id, elem_ty, false))) return false;
            }
            if (ap.has_rest and !ap.rest_binding.isNone()) {
                if (!(try checkPattern(self, ap.rest_binding.unwrap(), self.type_info.store.mkSlice(elem_ty), false))) return false;
            }
            return true;
        },
        // (duplicate Path handler removed)
        .Struct => {
            const sp = self.ast_unit.pats.get(.Struct, pid);
            const pattern_loc = self.ast_unit.exprs.locs.get(sp.loc);
            const value_kind = self.type_info.store.index.kinds.items[value_ty.toRaw()];
            if (value_kind != .Struct) {
                if (emit) try self.diags.addError(pattern_loc, .pattern_type_mismatch, .{});
                return false;
            }
            const value_struct_ty = self.type_info.store.Struct.get(self.type_info.store.index.rows.items[value_ty.toRaw()]);
            const pattern_fields = self.ast_unit.pats.field_pool.slice(sp.fields);
            const value_fields = self.type_info.store.field_pool.slice(value_struct_ty.fields);

            // For each pattern field, find a matching field in the value type and check recursively
            for (pattern_fields) |pat_field_id| {
                const pat_field = self.ast_unit.pats.StructField.get(pat_field_id.toRaw());
                var found_match = false;
                for (value_fields) |val_field_id| {
                    const val_field = self.type_info.store.Field.get(val_field_id.toRaw());
                    if (pat_field.name.toRaw() == val_field.name.toRaw()) {
                        found_match = true;
                        if (!(try checkPattern(self, pat_field.pattern, val_field.ty, false))) {
                            return false;
                        }
                        break;
                    }
                }
                if (!found_match) {
                    if (emit) try self.diags.addError(pattern_loc, .struct_pattern_field_mismatch, .{});
                    return false;
                }
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
    const subj_kind = self.type_info.store.index.kinds.items[subj_ty.toRaw()];
    const value_required = self.isValueReq();
    var result_ty: ?types.TypeId = null;

    // Exhaustiveness tracking (simple domains)
    var covered_true: bool = false;
    var covered_false: bool = false;
    var has_unguarded_wildcard: bool = false;
    var has_guarded_wildcard: bool = false;
    var bool_domain: bool = true; // all unguarded arms recognizable as bool-tag patterns
    var enum_domain: bool = true; // all unguarded arms recognizable as enum-tag patterns
    var unguarded_count: usize = 0;
    var enum_total: usize = 0;
    var enum_covered = std.AutoArrayHashMapUnmanaged(u32, void){};
    defer enum_covered.deinit(self.gpa);
    if (subj_kind == .Enum) {
        const er = self.type_info.store.Enum.get(self.type_info.store.index.rows.items[subj_ty.toRaw()]);
        enum_total = self.type_info.store.enum_member_pool.slice(er.members).len;
    }

    // Minimal immediate detection for integer overlap/unreachable (unguarded only)
    const is_int_subj = check_types.isIntegerKind(self, subj_kind);
    var int_seen_wildcard = false;
    var int_lit_set = std.AutoArrayHashMapUnmanaged(i64, void){};
    defer int_lit_set.deinit(self.gpa);
    var int_ranges = std.ArrayListUnmanaged(struct { a: i64, b: i64 }){};
    defer int_ranges.deinit(self.gpa);

    const arms = self.ast_unit.exprs.arm_pool.slice(mr.arms);
    var i: usize = 0;
    while (i < arms.len) : (i += 1) {
        const arm = self.ast_unit.exprs.MatchArm.get(arms[i].toRaw());

        // Validate pattern against subject type using existing pattern checker.
        const ok = try checkPattern(self, arm.pattern, subj_ty, false);
        if (!ok) {
            if (arms.len == 1) {
                const pk = self.ast_unit.pats.index.kinds.items[arm.pattern.toRaw()];
                const loc = self.ast_unit.exprs.locs.get(arm.loc);
                if (pk == .Struct or pk == .VariantStruct) {
                    try self.diags.addError(loc, .struct_pattern_field_mismatch, .{});
                } else {
                    try self.diags.addError(loc, .pattern_shape_mismatch, .{});
                }
                return null;
            } else continue;
        }

        // Guard must be boolean if present.
        if (!arm.guard.isNone()) {
            const gty = try self.checkExpr(arm.guard.unwrap());
            if (gty == null) return null;
            if (gty.?.toRaw() != self.type_info.store.tBool().toRaw()) {
                try self.diags.addError(self.ast_unit.exprs.locs.get(arm.loc), .non_boolean_condition, .{});
                return null;
            }
            // Track guarded wildcard for exhaustiveness info
            if (patternCoversWildcard(self, arm.pattern)) has_guarded_wildcard = true;
        } else {
            // Immediate overlap/unreachable detection for integer subjects, unguarded arms only
            if (is_int_subj) {
                const loc = self.ast_unit.exprs.locs.get(arm.loc);
                if (patternCoversWildcard(self, arm.pattern)) {
                    int_seen_wildcard = true;
                } else {
                    if (int_seen_wildcard) {
                        try self.diags.addError(loc, .unreachable_match_arm, .{});
                        return null;
                    }
                    if (patternIntLiteral(self, arm.pattern)) |lit| {
                        if (int_lit_set.contains(lit)) {
                            try self.diags.addError(loc, .overlapping_match_arm, .{});
                            return null;
                        }
                        var ri: usize = 0;
                        while (ri < int_ranges.items.len) : (ri += 1) {
                            const r = int_ranges.items[ri];
                            if (lit >= r.a and lit <= r.b) {
                                try self.diags.addError(loc, .overlapping_match_arm, .{});
                                return null;
                            }
                        }
                        _ = try int_lit_set.put(self.gpa, lit, {});
                    } else if (try patternIntRange(self, arm.pattern)) |rr| {
                        var rj: usize = 0;
                        while (rj < int_ranges.items.len) : (rj += 1) {
                            const r = int_ranges.items[rj];
                            if (!(rr.b < r.a or rr.a > r.b)) {
                                try self.diags.addError(loc, .overlapping_match_arm, .{});
                                return null;
                            }
                        }
                        var it = int_lit_set.iterator();
                        while (it.next()) |entry| {
                            const v = entry.key_ptr.*;
                            if (v >= rr.a and v <= rr.b) {
                                try self.diags.addError(loc, .overlapping_match_arm, .{});
                                return null;
                            }
                        }
                        try int_ranges.append(self.gpa, .{ .a = rr.a, .b = rr.b });
                    }
                }
            }
            // Track unguarded arms for exhaustiveness analysis
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

        // Check body and unify result when match is used as a value.
        const body_ty = try self.checkExpr(arm.body);
        if (!value_required) continue;
        if (body_ty == null) return null;
        if (result_ty == null) {
            result_ty = body_ty;
        } else if (result_ty.?.toRaw() != body_ty.?.toRaw()) {
            // Reuse if-branch mismatch diagnostic for now.
            try self.diags.addError(self.ast_unit.exprs.locs.get(mr.loc), .if_branch_type_mismatch, .{});
            return null;
        }
    }

    // Exhaustiveness post-pass (limited domains)
    var non_exhaustive = false;
    switch (subj_kind) {
        .Bool => {
            if (bool_domain and !has_unguarded_wildcard and !(covered_true and covered_false)) non_exhaustive = true;
        },
        .Enum => {
            if (enum_domain and !has_unguarded_wildcard and enum_total != 0 and enum_covered.count() < enum_total) non_exhaustive = true;
        },
        else => {
            // No domain coverage; but a purely guarded wildcard does not make it exhaustive
            if (unguarded_count == 0 and has_guarded_wildcard) non_exhaustive = true;
        },
    }
    if (non_exhaustive) {
        try self.diags.addError(self.ast_unit.exprs.locs.get(mr.loc), .non_exhaustive_match, .{});
        return null;
    }

    if (!value_required) return self.type_info.store.tVoid();
    return result_ty;
}

fn patternIntLiteral(self: *Checker, pid: ast.PatternId) ?i64 {
    const k = self.ast_unit.pats.index.kinds.items[pid.toRaw()];
    if (k != .Literal) return null;
    const lp = self.ast_unit.pats.get(.Literal, pid);
    if (self.ast_unit.exprs.index.kinds.items[lp.expr.toRaw()] != .Literal) return null;
    const lit = self.ast_unit.exprs.get(.Literal, lp.expr);
    if (lit.kind != .int or lit.value.isNone()) return null;
    const s = self.ast_unit.exprs.strs.get(lit.value.unwrap());
    return std.fmt.parseInt(i64, s, 10) catch null;
}

fn patternIntRange(self: *Checker, pid: ast.PatternId) !?struct { a: i64, b: i64 } {
    const k = self.ast_unit.pats.index.kinds.items[pid.toRaw()];
    if (k != .Range) return null;
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
    return .{ .a = a, .b = b };
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
        .Binding => blk_b: {
            const b = self.ast_unit.pats.get(.Binding, pid);
            const s = self.ast_unit.exprs.strs.get(b.name);
            if (std.mem.eql(u8, s, "true")) break :blk_b val == true;
            if (std.mem.eql(u8, s, "false")) break :blk_b val == false;
            break :blk_b false;
        },
        .Path => blk_p: {
            const pp = self.ast_unit.pats.get(.Path, pid);
            const segs = self.ast_unit.pats.seg_pool.slice(pp.segments);
            if (segs.len == 0) break :blk_p false;
            const last = self.ast_unit.pats.PathSeg.get(segs[segs.len - 1].toRaw());
            const s = self.ast_unit.exprs.strs.get(last.name);
            if (std.mem.eql(u8, s, "true")) break :blk_p val == true;
            if (std.mem.eql(u8, s, "false")) break :blk_p val == false;
            break :blk_p false;
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

fn recordEnumTagsCovered(self: *Checker, pid: ast.PatternId, enum_ty: types.TypeId, out: *std.AutoArrayHashMapUnmanaged(u32, void)) !void {
    const k = self.ast_unit.pats.index.kinds.items[pid.toRaw()];
    switch (k) {
        .Path => {
            const pp = self.ast_unit.pats.get(.Path, pid);
            const segs = self.ast_unit.pats.seg_pool.slice(pp.segments);
            if (segs.len == 0) return;
            const last = self.ast_unit.pats.PathSeg.get(segs[segs.len - 1].toRaw());
            const er = self.type_info.store.Enum.get(self.type_info.store.index.rows.items[enum_ty.toRaw()]);
            const members = self.type_info.store.enum_member_pool.slice(er.members);
            for (members) |mid| {
                const m = self.type_info.store.EnumMember.get(mid.toRaw());
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

fn isBoolPattern(self: *Checker, pid: ast.PatternId) bool {
    const k = self.ast_unit.pats.index.kinds.items[pid.toRaw()];
    return switch (k) {
        .Wildcard => true,
        .Literal => patternCoversBoolValue(self, pid, true) or patternCoversBoolValue(self, pid, false),
        .Or => blk: {
            const op = self.ast_unit.pats.get(.Or, pid);
            const alts = self.ast_unit.pats.pat_pool.slice(op.alts);
            for (alts) |aid| if (!isBoolPattern(self, aid)) break :blk false;
            break :blk true;
        },
        .At => isBoolPattern(self, self.ast_unit.pats.get(.At, pid).pattern),
        else => false,
    };
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
            const er = self.type_info.store.Enum.get(self.type_info.store.index.rows.items[enum_ty.toRaw()]);
            const members = self.type_info.store.enum_member_pool.slice(er.members);
            for (members) |mid| {
                const m = self.type_info.store.EnumMember.get(mid.toRaw());
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
    if (self.type_info.store.index.kinds.items[value_ty.toRaw()] != .Struct) return false;
    const sp = self.ast_unit.pats.get(.Struct, pid);
    const value_struct_ty = self.type_info.store.Struct.get(self.type_info.store.index.rows.items[value_ty.toRaw()]);
    const pattern_fields = self.ast_unit.pats.field_pool.slice(sp.fields);
    const value_fields = self.type_info.store.field_pool.slice(value_struct_ty.fields);
    for (pattern_fields) |pat_field_id| {
        const pat_field = self.ast_unit.pats.StructField.get(pat_field_id.toRaw());
        var found = false;
        for (value_fields) |val_field_id| {
            const val_field = self.type_info.store.Field.get(val_field_id.toRaw());
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
            const row: symbols.SymbolRow = switch (origin) {
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
            _ = try self.symtab.declare(row);
            // If nested pattern under binding exists, declare inner bindings as well
            // if (!b.pattern.isNone()) try self.declareBindingsInPattern(b.pattern.unwrap(), loc, origin);
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
        .Path => {
            // Paths in patterns are heads (e.g., Type/Constructor) or constants, not bindings.
            // Do not declare any symbol for path segments here.
        },
        .Literal => {},
        else => {},
    }
}

const PatternShapeCheck = enum { ok, tuple_arity_mismatch, struct_field_mismatch, shape_mismatch };
pub fn checkPatternShapeForDecl(self: *Checker, pid: ast.PatternId, value_ty: types.TypeId) PatternShapeCheck {
    const pkind = self.type_info.store.index.kinds.items[value_ty.toRaw()];
    const k = self.ast_unit.pats.index.kinds.items[pid.toRaw()];
    switch (k) {
        .Wildcard, .Binding => return .ok,
        .Tuple => {
            if (pkind != .Tuple) return .shape_mismatch;
            const tp = self.type_info.store.Tuple.get(self.type_info.store.index.rows.items[value_ty.toRaw()]);
            const vals = self.type_info.store.type_pool.slice(tp.elems);
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
            const sv = self.type_info.store.Struct.get(self.type_info.store.index.rows.items[value_ty.toRaw()]);
            const vfields = self.type_info.store.field_pool.slice(sv.fields);
            const sp = self.ast_unit.pats.get(.Struct, pid);
            const pfields = self.ast_unit.pats.field_pool.slice(sp.fields);
            // every pattern field must exist by name
            var i: usize = 0;
            while (i < pfields.len) : (i += 1) {
                const pf = self.ast_unit.pats.StructField.get(pfields[i].toRaw());
                var found: ?types.TypeId = null;
                var j: usize = 0;
                while (j < vfields.len) : (j += 1) {
                    const vf = self.type_info.store.Field.get(vfields[j].toRaw());
                    if (vf.name.toRaw() == pf.name.toRaw()) {
                        found = vf.ty;
                        break;
                    }
                }
                if (found == null) return .struct_field_mismatch;
                const res = checkPatternShapeForDecl(self, pf.pattern, found.?);
                if (res != .ok) return res;
            }
            return .ok;
        },
        .Slice => {
            // Accept array/slice/dynarray; recurse on element patterns
            if (pkind != .Array and pkind != .Slice and pkind != .DynArray) return .shape_mismatch;
            const elem_ty: types.TypeId = switch (pkind) {
                .Array => self.type_info.store.Array.get(self.type_info.store.index.rows.items[value_ty.toRaw()]).elem,
                .Slice => self.type_info.store.Slice.get(self.type_info.store.index.rows.items[value_ty.toRaw()]).elem,
                .DynArray => self.type_info.store.DynArray.get(self.type_info.store.index.rows.items[value_ty.toRaw()]).elem,
                else => unreachable,
            };
            const sl = self.ast_unit.pats.get(.Slice, pid);
            const elems = self.ast_unit.pats.pat_pool.slice(sl.elems);
            // Fixed-size array arity check
            if (pkind == .Array) {
                const arr = self.type_info.store.Array.get(self.type_info.store.index.rows.items[value_ty.toRaw()]);
                if (sl.has_rest) {
                    // With rest anywhere (Rust-like), only require explicit elements <= length
                    if (elems.len >= arr.len) return .shape_mismatch;
                } else {
                    if (elems.len != arr.len) return .shape_mismatch;
                }
            }
            // Check explicit element subpatterns against element type
            for (elems) |eid| {
                const res = checkPatternShapeForDecl(self, eid, elem_ty);
                if (res != .ok) return res;
            }
            if (sl.has_rest and !sl.rest_binding.isNone()) {
                // rest binding gets slice<elem_ty>
                const rest_res = checkPatternShapeForDecl(self, sl.rest_binding.unwrap(), self.type_info.store.mkSlice(elem_ty));
                if (rest_res != .ok) return rest_res;
            }
            return .ok;
        },
        .Path, .Literal => return .ok,
        else => return .ok,
    }
}

pub fn checkPatternShapeForAssignExpr(self: *Checker, expr: ast.ExprId, value_ty: types.TypeId) PatternShapeCheck {
    const vk = self.type_info.store.index.kinds.items[value_ty.toRaw()];
    const k = self.ast_unit.exprs.index.kinds.items[expr.toRaw()];
    switch (k) {
        .Ident => return .ok,
        .TupleLit => {
            if (vk != .Tuple) return .shape_mismatch;
            const tl = self.ast_unit.exprs.get(.TupleLit, expr);
            const elems = self.ast_unit.exprs.expr_pool.slice(tl.elems);
            const trow = self.type_info.store.Tuple.get(self.type_info.store.index.rows.items[value_ty.toRaw()]);
            const tys = self.type_info.store.type_pool.slice(trow.elems);
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
            const sv = self.type_info.store.Struct.get(self.type_info.store.index.rows.items[value_ty.toRaw()]);
            const vfields = self.type_info.store.field_pool.slice(sv.fields);
            const sl = self.ast_unit.exprs.get(.StructLit, expr);
            const pfields = self.ast_unit.exprs.sfv_pool.slice(sl.fields);
            var i: usize = 0;
            while (i < pfields.len) : (i += 1) {
                const pf = self.ast_unit.exprs.StructFieldValue.get(pfields[i].toRaw());
                if (pf.name.isNone()) return .shape_mismatch;
                var fty: ?types.TypeId = null;
                var j: usize = 0;
                while (j < vfields.len) : (j += 1) {
                    const vf = self.type_info.store.Field.get(vfields[j].toRaw());
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
                .Array => self.type_info.store.Array.get(self.type_info.store.index.rows.items[value_ty.toRaw()]).elem,
                .Slice => self.type_info.store.Slice.get(self.type_info.store.index.rows.items[value_ty.toRaw()]).elem,
                .DynArray => self.type_info.store.DynArray.get(self.type_info.store.index.rows.items[value_ty.toRaw()]).elem,
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
                    if (has_rest) return .shape_mismatch; // multiple rest
                    has_rest = true;
                    rest_index = i;
                    // rest binding type check: expect slice<elem_ty> — handled via recursion below
                    continue;
                }
                const res = checkPatternShapeForAssignExpr(self, elems[i], elem_ty);
                if (res != .ok) return res;
            }
            if (vk == .Array) {
                const arr = self.type_info.store.Array.get(self.type_info.store.index.rows.items[value_ty.toRaw()]);
                if (has_rest) {
                    if (elems.len - 1 > arr.len) return .shape_mismatch; // minus the rest placeholder
                } else {
                    if (elems.len != arr.len) return .shape_mismatch;
                }
            }
            // If there is a rest binding, ensure it is a binding/wildcard shape
            if (has_rest) {
                const r = self.ast_unit.exprs.get(.ArrayLit, expr);
                const es = self.ast_unit.exprs.expr_pool.slice(r.elems);
                const rest_expr = es[rest_index];
                const rr = self.ast_unit.exprs.get(.Range, rest_expr);
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
    const pk = self.type_info.store.index.kinds.items[value_ty.toRaw()];
    const k = self.ast_unit.pats.index.kinds.items[pid.toRaw()];
    switch (k) {
        .Binding => {
            const b = self.ast_unit.pats.get(.Binding, pid);
            if (b.name.toRaw() == name.toRaw()) return value_ty;
            return null;
        },
        .Wildcard => return null,
        .Tuple => {
            if (pk != .Tuple) return null;
            const tp = self.type_info.store.Tuple.get(self.type_info.store.index.rows.items[value_ty.toRaw()]);
            const elems_ty = self.type_info.store.type_pool.slice(tp.elems);
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
            const st = self.type_info.store.Struct.get(self.type_info.store.index.rows.items[value_ty.toRaw()]);
            const fields_ty = self.type_info.store.field_pool.slice(st.fields);
            const sp = self.ast_unit.pats.get(.Struct, pid);
            const fields = self.ast_unit.pats.field_pool.slice(sp.fields);
            for (fields) |fid| {
                const pf = self.ast_unit.pats.StructField.get(fid.toRaw());
                var i: usize = 0;
                while (i < fields_ty.len) : (i += 1) {
                    const tf = self.type_info.store.Field.get(fields_ty[i].toRaw());
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
            // For now, map all element-pattern bindings to the element type
            const elem_ty: types.TypeId = switch (pk) {
                .Array => self.type_info.store.Array.get(self.type_info.store.index.rows.items[value_ty.toRaw()]).elem,
                .Slice => self.type_info.store.Slice.get(self.type_info.store.index.rows.items[value_ty.toRaw()]).elem,
                .DynArray => self.type_info.store.DynArray.get(self.type_info.store.index.rows.items[value_ty.toRaw()]).elem,
                else => return null,
            };
            const sl = self.ast_unit.pats.get(.Slice, pid);
            const elems = self.ast_unit.pats.pat_pool.slice(sl.elems);
            for (elems) |eid| if (bindingTypeInPattern(self, eid, name, elem_ty)) |bt| return bt;
            if (sl.has_rest and !sl.rest_binding.isNone()) {
                // Rest binding receives a slice of element type
                const rest_ty = self.type_info.store.mkSlice(elem_ty);
                if (bindingTypeInPattern(self, sl.rest_binding.unwrap(), name, rest_ty)) |bt| return bt;
            }
            return null;
        },
        .Path, .Literal => return null,
        else => return null,
    }
}
