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
    const k = self.typeKind(ty);
    return if (k == .Variant)
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

/// Inclusive integer interval used while tracking range patterns.
const Interval = struct {
    a: i64,
    b: i64,
};

/// Accumulates the literals/ranges extracted from an integer pattern.
const IntSet = struct {
    /// Tracks whether the pattern covers every integer (wildcard `_` or similar).
    wildcard: bool = false,
    /// Set when encountering non-integer patterns so we skip specialized analysis.
    non_int: bool = false,
    /// Individual literal integers collected from the pattern.
    points: std.ArrayListUnmanaged(i64) = .{},
    /// Inclusive intervals derived from range patterns.
    ranges: std.ArrayListUnmanaged(Interval) = .{},

    /// Release the temporary lists that track matched integers/ranges.
    pub fn deinit(self: *IntSet, gpa: std.mem.Allocator) void {
        self.points.deinit(gpa);
        self.ranges.deinit(gpa);
    }
};

/// Tracks which integer values/intervals have been covered so far.
const IntCoverage = struct {
    /// Wildcard coverage indicates `_` matched already.
    wildcard: bool = false,
    /// Covered literal integers (no duplicates).
    points: std.AutoArrayHashMapUnmanaged(i64, void) = .{},
    /// Non-overlapping, sorted intervals (merged when adjacent).
    ranges: std.ArrayList(Interval) = .{},

    pub fn deinit(self: *IntCoverage, gpa: std.mem.Allocator) void {
        self.points.deinit(gpa);
        self.ranges.deinit(gpa);
    }
};

/// Return true if intervals `a` and `b` overlap or touch.
inline fn intervalOverlaps(a: Interval, b: Interval) bool {
    return !(a.b < b.a or a.a > b.b);
}
/// Return true when point `p` falls within interval `r`.
inline fn pointInInterval(p: i64, r: Interval) bool {
    return p >= r.a and p <= r.b;
}

/// Flattens `pid` into integer points/intervals for exhaustiveness checks.
fn collectIntSet(self: *Checker, ast_unit: *ast.Ast, pid: ast.PatternId, out: *IntSet) !void {
    switch (ast_unit.kind(pid)) {
        .Wildcard => out.wildcard = true,
        .Literal => if (patternIntLiteral(self, ast_unit, pid)) |lit| {
            try out.points.append(self.gpa, lit);
        } else {
            out.non_int = true;
        },
        .Range => if (try patternIntRange(self, ast_unit, pid)) |rr| {
            try out.ranges.append(self.gpa, .{ .a = rr.a, .b = rr.b });
        } else {
            // either not an int range or invalid/empty
            out.non_int = true;
        },
        .Or => {
            const op = ast_unit.pats.get(.Or, pid);
            const alts = ast_unit.pats.pat_pool.slice(op.alts);
            for (alts) |aid| {
                try collectIntSet(self, ast_unit, aid, out);
                if (out.wildcard) break; // early if already everything
            }
        },
        .At => try collectIntSet(self, ast_unit, ast_unit.pats.get(.At, pid).pattern, out),
        // everything else: treat as "non-int" for this specialized analysis
        else => out.non_int = true,
    }
}

/// Try adding literal `lit` into `cov` and report whether it overlaps earlier points.
fn coverAddPointDetectOverlap(self: *Checker, cov: *IntCoverage, lit: i64) !bool {
    if (cov.points.contains(lit)) return true;
    var i: usize = 0;
    while (i < cov.ranges.items.len) : (i += 1)
        if (pointInInterval(lit, cov.ranges.items[i]))
            return true;

    try cov.points.put(self.gpa, lit, {});
    return false;
}

/// Insert interval `new` into the coverage set, merging and detecting overlaps.
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

fn checkOrPattern(self: *Checker, ctx: *Checker.CheckerContext, ast_unit: *ast.Ast, pid: ast.PatternId, value_ty: types.TypeId) !bool {
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
            const idx = self.context.diags.messages.items.len;
            try self.context.diags.addError(ast_unit.exprs.locs.get(op.loc), .or_pattern_binding_mismatch, .{});
            try self.context.diags.attachNote(idx, null, .pattern_binding_help);
            return false;
        }

        for (first_bindings.items) |b1_name| {
            var found = false;
            for (alt_bindings.items) |b2_name| {
                if (!b1_name.eq(b2_name)) continue;
                const b1_ty = bindingTypeInPattern(self, ast_unit, alts[0], b1_name, value_ty);
                const b2_ty = bindingTypeInPattern(self, ast_unit, alt_id, b2_name, value_ty);
                if (b1_ty == null or b2_ty == null or !b1_ty.?.eq(b2_ty.?)) {
                    const idx = self.context.diags.messages.items.len;
                    try self.context.diags.addError(ast_unit.exprs.locs.get(op.loc), .or_pattern_binding_type_mismatch, .{});
                    try self.context.diags.attachNote(idx, null, .pattern_binding_help);
                    return false;
                }
                found = true;
                break;
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
        const ok = try checkPattern(self, ctx, ast_unit, aid, value_ty, false);
        any_ok = any_ok or ok;
    }
    return any_ok;
}

fn checkRangePattern(self: *Checker, ctx: *Checker.CheckerContext, ast_unit: *ast.Ast, pid: ast.PatternId, value_ty: types.TypeId) !bool {
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
        if (ast_unit.kind(sid) == .Literal and ast_unit.kind(eid) == .Literal) {
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
}

fn checkVariantTuplePattern(self: *Checker, ctx: *Checker.CheckerContext, ast_unit: *ast.Ast, pid: ast.PatternId, value_ty: types.TypeId) !bool {
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
}

fn checkVariantStructPattern(self: *Checker, ctx: *Checker.CheckerContext, ast_unit: *ast.Ast, pid: ast.PatternId, value_ty: types.TypeId) !bool {
    const vs_pat = ast_unit.pats.get(.VariantStruct, pid);
    const vk = self.typeKind(value_ty);

    // Struct sugar: allow `Type { ... }` against a struct value.
    if (vk != .Variant and vk != .Error) {
        if (vk == .Struct) {
            const st = self.context.type_store.get(.Struct, value_ty);
            const value_fields = self.context.type_store.field_pool.slice(st.fields);
            const pat_fields = ast_unit.pats.field_pool.slice(vs_pat.fields);
            var field_map: std.AutoArrayHashMap(ast.StrId, types.TypeId) = .init(self.gpa);
            defer field_map.deinit();
            for (value_fields) |vfid| {
                const vf = self.context.type_store.Field.get(vfid);
                _ = try field_map.put(vf.name, vf.ty);
            }

            for (pat_fields) |pfid| {
                const pf = ast_unit.pats.StructField.get(pfid);
                const fty = field_map.get(pf.name);
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
    var field_map: std.AutoArrayHashMap(ast.StrId, types.TypeId) = .init(self.gpa);
    defer field_map.deinit();
    for (value_fields) |vfid| {
        const vf = self.context.type_store.Field.get(vfid);
        _ = try field_map.put(vf.name, vf.ty);
    }

    for (pat_fields) |pfid| {
        const pf = ast_unit.pats.StructField.get(pfid);
        const fty = field_map.get(pf.name);
        if (fty == null) return false;
        if (!(try checkPattern(self, ctx, ast_unit, pf.pattern, fty.?, false))) {
            try self.context.diags.addError(ast_unit.exprs.locs.get(vs_pat.loc), .struct_pattern_field_mismatch, .{});
            return false;
        }
    }
    return true;
}

fn checkPathPattern(self: *Checker, ctx: *Checker.CheckerContext, ast_unit: *ast.Ast, pid: ast.PatternId, value_ty: types.TypeId) !bool {
    _ = ctx;
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
                if (m.name.eq(last.name)) return true;
            }
            return false;
        },
        .Variant, .Error => {
            const cases = getVariantOrErrorCases(self, value_ty);
            for (cases) |fid| {
                const f = self.context.type_store.Field.get(fid);
                if (f.name.eq(last.name)) {
                    // tag-only allowed only when payload is void
                    return self.typeKind(f.ty) == .Void;
                }
            }
            return false;
        },
        else => return false,
    }
}

fn checkLiteralPattern(self: *Checker, ctx: *Checker.CheckerContext, ast_unit: *ast.Ast, pid: ast.PatternId, value_ty: types.TypeId, emit: bool) !bool {
    // Literal patterns must type-check against subject type.
    const lp = ast_unit.pats.get(.Literal, pid);
    const pattern_loc = ast_unit.exprs.locs.get(lp.loc);
    const lit_expr_id = lp.expr;
    const lit_ty = try self.checkExpr(ctx, ast_unit, lit_expr_id);
    if (self.typeKind(lit_ty) == .TypeError) return false;
    if (self.typeKind(lit_ty) == .String) {
        if (emit) try self.context.diags.addError(pattern_loc, .string_equality_in_match_not_supported, .{});
        return false;
    }

    if (self.assignable(value_ty, lit_ty) != .success) {
        if (emit) try self.context.diags.addError(pattern_loc, .pattern_type_mismatch, .{});
        return false;
    }
    // Future: evaluate and compare values if not top-level.
    return true;
}

fn checkTuplePattern(self: *Checker, ctx: *Checker.CheckerContext, ast_unit: *ast.Ast, pid: ast.PatternId, value_ty: types.TypeId, emit: bool) !bool {
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
}

fn checkSlicePattern(self: *Checker, ctx: *Checker.CheckerContext, ast_unit: *ast.Ast, pid: ast.PatternId, value_ty: types.TypeId, emit: bool) !bool {
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
        if (ap.has_rest) {
            if (pattern_elems.len > arr.len) return false;
        } else {
            if (pattern_elems.len != arr.len) return false;
        }
    }

    for (pattern_elems, 0..) |pat_elem_id, i| {
        if (ap.has_rest and i == ap.rest_index) continue; // skip the rest placeholder
        if (!(try checkPattern(self, ctx, ast_unit, pat_elem_id, elem_ty, false))) return false;
    }

    if (ap.has_rest and !ap.rest_binding.isNone()) {
        const rest_const = if (vk == .Slice)
            self.context.type_store.get(.Slice, value_ty).is_const
        else
            false;
        if (!(try checkPattern(self, ctx, ast_unit, ap.rest_binding.unwrap(), self.context.type_store.mkSlice(elem_ty, rest_const), false)))
            return false;
    }
    return true;
}

fn checkStructPattern(self: *Checker, ctx: *Checker.CheckerContext, ast_unit: *ast.Ast, pid: ast.PatternId, value_ty: types.TypeId, emit: bool) !bool {
    const sp = ast_unit.pats.get(.Struct, pid);
    const pattern_loc = ast_unit.exprs.locs.get(sp.loc);
    if (self.typeKind(value_ty) != .Struct) {
        if (emit) try self.context.diags.addError(pattern_loc, .pattern_type_mismatch, .{});
        return false;
    }
    const value_struct_ty = self.context.type_store.get(.Struct, value_ty);
    const pattern_fields = ast_unit.pats.field_pool.slice(sp.fields);
    const value_fields = self.context.type_store.field_pool.slice(value_struct_ty.fields);
    var field_map: std.AutoArrayHashMap(ast.StrId, types.TypeId) = .init(self.gpa);
    defer field_map.deinit();
    for (value_fields) |val_field_id| {
        const val_field = self.context.type_store.Field.get(val_field_id);
        _ = try field_map.put(val_field.name, val_field.ty);
    }

    for (pattern_fields) |pat_field_id| {
        const pat_field = ast_unit.pats.StructField.get(pat_field_id);
        const match_ty = field_map.get(pat_field.name);

        if (match_ty == null) {
            if (emit) try self.context.diags.addError(pattern_loc, .struct_pattern_field_mismatch, .{});
            return false;
        }
        if (!(try checkPattern(self, ctx, ast_unit, pat_field.pattern, match_ty.?, false))) return false;
    }
    return true;
}

/// Validate that `pid` matches `value_ty`, emitting diagnostics when pattern shapes deviate.
pub fn checkPattern(
    self: *Checker,
    ctx: *Checker.CheckerContext,
    ast_unit: *ast.Ast,
    pid: ast.PatternId,
    value_ty: types.TypeId,
    top_level: bool,
) anyerror!bool {
    // Emit diagnostics only on top-level shape checks, but keep inner calls quiet.
    const emit = top_level;
    return switch (ast_unit.kind(pid)) {
        .Or => checkOrPattern(self, ctx, ast_unit, pid, value_ty),
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
            return try checkPattern(self, ctx, ast_unit, ap.pattern, value_ty, emit);
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
        .Range => checkRangePattern(self, ctx, ast_unit, pid, value_ty),
        .VariantTuple => checkVariantTuplePattern(self, ctx, ast_unit, pid, value_ty),
        .Path => checkPathPattern(self, ctx, ast_unit, pid, value_ty),
        .VariantStruct => checkVariantStructPattern(self, ctx, ast_unit, pid, value_ty),
        .Wildcard => true,
        .Literal => checkLiteralPattern(self, ctx, ast_unit, pid, value_ty, emit),
        .Tuple => checkTuplePattern(self, ctx, ast_unit, pid, value_ty, emit),
        .Slice => checkSlicePattern(self, ctx, ast_unit, pid, value_ty, emit),
        .Struct => checkStructPattern(self, ctx, ast_unit, pid, value_ty, emit),
    };
}

/// Check the `match` expression at `id`, ensuring all arms are consistent and returning its resultant type.
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
    var enum_covered = std.AutoArrayHashMapUnmanaged(ast.StrId, void){};
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
            if (!gty.eq(self.context.type_store.tBool())) {
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
        } else if (!result_ty.?.eq(body_ty)) {
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
        var missing_cases: ?ast.StrId = null;
        switch (subj_kind) {
            .Bool => missing_cases = try missingBoolMatchCases(self, covered_true, covered_false),
            .Enum => missing_cases = try missingEnumMatchCases(self, subj_ty, &enum_covered),
            else => {},
        }
        const diag_idx = self.context.diags.count();
        try self.context.diags.addError(ast_unit.exprs.locs.get(mr.loc), .non_exhaustive_match, .{});

        if (missing_cases) |cases| {
            try self.context.diags.attachNoteArgs(diag_idx, null, .exhaustiveness_hint, checker.StringNotePayload{ .value = cases });
        }
        const wildcard_example: []const u8 = "_ => {}"[0..];
        try self.context.diags.attachNoteArgs(diag_idx, null, .add_wildcard, .{wildcard_example});
        return self.context.type_store.tTypeError();
    }

    if (!value_required) return self.context.type_store.tVoid();
    return result_ty orelse self.context.type_store.tVoid();
}

/// Extract an integer literal value if `pid` is an integer literal (possibly wrapped with `@`).
/// If `pid` is an integer literal pattern, return its value.
fn patternIntLiteral(self: *Checker, ast_unit: *ast.Ast, pid: ast.PatternId) ?i64 {
    switch (ast_unit.kind(pid)) {
        .Literal => {
            const lp = ast_unit.pats.get(.Literal, pid);
            if (ast_unit.kind(lp.expr) != .Literal) return null;
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

/// Extract the inclusive integer interval described by `pid`, returning null for invalid ranges.
fn patternIntRange(self: *Checker, ast_unit: *ast.Ast, pid: ast.PatternId) !?struct { a: i64, b: i64 } {
    switch (ast_unit.kind(pid)) {
        .Range => {
            const rp = ast_unit.pats.get(.Range, pid);
            if (rp.start.isNone() or rp.end.isNone()) return null;
            const sid = rp.start.unwrap();
            const eid = rp.end.unwrap();
            if (ast_unit.kind(sid) != .Literal or ast_unit.kind(eid) != .Literal) return null;
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

/// Return true when the pattern `pid` definitely matches all values (e.g., `_` or `Or` of wildcards).
fn patternCoversWildcard(self: *Checker, ast_unit: *ast.Ast, pid: ast.PatternId) bool {
    return switch (ast_unit.kind(pid)) {
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

/// Determine whether pattern `pid` covers the boolean literal `val`.
fn patternCoversBoolValue(self: *Checker, ast_unit: *ast.Ast, pid: ast.PatternId, val: bool) bool {
    return switch (ast_unit.kind(pid)) {
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
            if (ast_unit.kind(lp.expr) != .Literal) break :blk false;
            const lit = ast_unit.exprs.get(.Literal, lp.expr);
            if (lit.kind != .bool) break :blk false;
            const lit_val = switch (lit.data) {
                .bool => |b| b,
                else => break :blk false,
            };
            break :blk (lit_val == val);
        },
        .Or => blk: {
            const op = ast_unit.pats.get(.Or, pid);
            const alts = ast_unit.pats.pat_pool.slice(op.alts);
            for (alts) |aid|
                if (patternCoversBoolValue(self, ast_unit, aid, val)) break :blk true;
            break :blk false;
        },
        .At => patternCoversBoolValue(self, ast_unit, ast_unit.pats.get(.At, pid).pattern, val),
        else => false,
    };
}

/// Record which enum tags are present in `rst` and return whether `tag` already covered.
fn recordEnumTagsCovered(
    self: *Checker,
    ast_unit: *ast.Ast,
    pid: ast.PatternId,
    enum_ty: types.TypeId,
    out: *std.AutoArrayHashMapUnmanaged(ast.StrId, void),
) !void {
    switch (ast_unit.kind(pid)) {
        .Path => {
            const pp = ast_unit.pats.get(.Path, pid);
            const segs = ast_unit.pats.seg_pool.slice(pp.segments);
            if (segs.len == 0) return;
            const last = ast_unit.pats.PathSeg.get(segs[segs.len - 1]);
            const er = self.context.type_store.get(.Enum, enum_ty);
            const members = self.context.type_store.enum_member_pool.slice(er.members);
            for (members) |mid| {
                const m = self.context.type_store.EnumMember.get(mid);
                if (m.name.eq(last.name)) {
                    _ = try out.put(self.gpa, m.name, {});
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

/// Return true when `pid` looks like it matches enum tags only (no nested structure).
fn isEnumTagPattern(self: *Checker, ast_unit: *ast.Ast, pid: ast.PatternId, enum_ty: types.TypeId) bool {
    return switch (ast_unit.kind(pid)) {
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
                if (m.name.eq(last.name)) break :blk true;
            }
            break :blk false;
        },
        .Or => blk: {
            const op = ast_unit.pats.get(.Or, pid);
            const alts = ast_unit.pats.pat_pool.slice(op.alts);
            for (alts) |aid|
                if (!isEnumTagPattern(self, ast_unit, aid, enum_ty)) break :blk false;
            break :blk true;
        },
        .At => isEnumTagPattern(self, ast_unit, ast_unit.pats.get(.At, pid).pattern, enum_ty),
        else => false,
    };
}

/// Return true when struct pattern `pid` references only existing fields of `value_ty`.
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
            if (pat_field.name.eq(val_field.name)) {
                found = true;
                break;
            }
        }
        if (!found) return false;
    }
    return true;
}

/// Return a comma-separated list of missing boolean match cases (if any) for diagnostics.
fn missingBoolMatchCases(self: *Checker, covered_true: bool, covered_false: bool) !?ast.StrId {
    var missing = std.ArrayList([]const u8){};
    defer missing.deinit(self.gpa);
    if (!covered_true) try missing.append(self.gpa, "true");
    if (!covered_false) try missing.append(self.gpa, "false");
    if (missing.items.len == 0) return null;
    const joined = try diag.joinStrings(self.gpa, ", ", missing.items);
    const joined_id = self.context.interner.intern(joined);
    self.gpa.free(joined);
    return joined_id;
}

/// Format enum tag names that remain uncovered by match arms for diagnostics.
fn missingEnumMatchCases(
    self: *Checker,
    enum_ty: types.TypeId,
    covered: *std.AutoArrayHashMapUnmanaged(ast.StrId, void),
) !?ast.StrId {
    var missing = std.ArrayList([]const u8){};
    defer missing.deinit(self.gpa);
    const members = self.context.type_store.enum_member_pool.slice(self.context.type_store.get(.Enum, enum_ty).members);
    for (members) |mid| {
        const member = self.context.type_store.EnumMember.get(mid);
        if (covered.get(member.name) != null) continue;
        const name = self.context.interner.get(member.name);
        try missing.append(self.gpa, name);
    }
    if (missing.items.len == 0) return null;
    const joined = try diag.joinStrings(self.gpa, ", ", missing.items);
    const joined_id = self.context.interner.intern(joined);
    self.gpa.free(joined);
    return joined_id;
}

/// Metadata that records whether a pattern binding stems from a declaration, parameter, or is anonymous.
pub const BindingOrigin = union(enum) {
    /// Binding declared as part of a declaration (maps to `DeclId`).
    decl: ast.DeclId,
    /// Binding associated with a parameter (maps to `ParamId`).
    param: ast.ParamId,
    /// Anonymous binding (no declaration/parameter metadata).
    anonymous,
};

/// Register bindings introduced by `pid` into the symbol table with origin metadata.
pub fn declareBindingsInPattern(
    self: *Checker,
    ctx: *Checker.CheckerContext,
    ast_unit: *ast.Ast,
    pid: ast.PatternId,
    loc: ast.LocId,
    origin: BindingOrigin,
) !void {
    var declarer = PatternBindingDeclarer{
        .checker = self,
        .ctx = ctx,
        .loc = loc,
        .origin = origin,
    };
    var walker_ctx = check_types.PatternWalkerContext{
        .ctx = @ptrCast(@alignCast(&declarer)),
        .onExpr = null,
        .onBinding = patternBindingDeclarerOnBinding,
        .onChildType = null,
    };
    try check_types.walkPattern(&walker_ctx, ast_unit, pid, null);
}

const PatternBindingDeclarer = struct {
    checker: *Checker,
    ctx: *Checker.CheckerContext,
    loc: ast.LocId,
    origin: BindingOrigin,

    fn buildSymbol(self: *PatternBindingDeclarer, ast_unit: *ast.Ast, name: ast.StrId) !symbols.SymbolRow {
        return switch (self.origin) {
            .decl => |did| blk: {
                const decl = ast_unit.exprs.Decl.get(did);
                const rhs_kind = ast_unit.kind(decl.value);
                const is_comptime_val = switch (rhs_kind) {
                    .Literal, .MlirBlock, .TupleType, .ArrayType, .DynArrayType, .SliceType, .OptionalType, .ErrorSetType, .ErrorType, .StructType, .EnumType, .VariantType, .UnionType, .PointerType, .SimdType, .ComplexType, .TensorType, .TypeType, .AnyType, .NoreturnType, .MapType, .ComptimeBlock, .TypeOf => true,
                    else => false,
                };
                break :blk .{
                    .name = name,
                    .kind = .Var,
                    .is_comptime = is_comptime_val,
                    .loc = self.loc,
                    .origin_decl = .some(did),
                    .origin_param = .none(),
                };
            },
            .param => |par| .{
                .name = name,
                .kind = .Param,
                .is_comptime = ast_unit.exprs.Param.get(par).is_comptime,
                .loc = self.loc,
                .origin_decl = .none(),
                .origin_param = .some(par),
            },
            .anonymous => .{
                .name = name,
                .kind = .Var,
                .is_comptime = false,
                .loc = self.loc,
                .origin_decl = .none(),
                .origin_param = .none(),
            },
        };
    }
};

fn patternBindingDeclarerOnBinding(ctx: *void, ast_unit: *ast.Ast, _: ast.PatternId, name: ast.StrId, _: ?types.TypeId) anyerror!void {
    const declarer: *PatternBindingDeclarer = @ptrCast(@alignCast(ctx));
    const symbol = try declarer.buildSymbol(ast_unit, name);
    _ = try declarer.ctx.symtab.declare(symbol);
    return;
}

/// Result of aligning a pattern with a target value type.
const PatternShapeCheck = enum {
    /// Pattern matches the target shape without issues.
    ok,
    /// Tuple literal has a different number of elements than the type.
    tuple_arity_mismatch,
    /// Struct pattern names fields that the type does not expose.
    struct_pattern_field_mismatch,
    /// The pattern and type belong to entirely different data shapes.
    pattern_shape_mismatch,
};

/// Ensure the pattern `pid` fits the shape of `value_ty` when used in a declaration binding.
pub fn checkPatternShapeForDecl(
    self: *Checker,
    ast_unit: *ast.Ast,
    pid: ast.PatternId,
    value_ty: types.TypeId,
) PatternShapeCheck {
    const pkind = self.typeKind(value_ty);
    switch (ast_unit.kind(pid)) {
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
                    if (vf.name.eq(pf.name)) {
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
                if (sl.has_rest) {
                    if (elems.len > arr.len) return .pattern_shape_mismatch;
                } else {
                    if (elems.len != arr.len) return .pattern_shape_mismatch;
                }
            }

            for (elems) |eid| {
                const res = checkPatternShapeForDecl(self, ast_unit, eid, elem_ty);
                if (res != .ok) return res;
            }
            if (sl.has_rest and !sl.rest_binding.isNone()) {
                const rest_const = if (pkind == .Slice)
                    self.context.type_store.get(.Slice, value_ty).is_const
                else
                    false;
                const rest_res = checkPatternShapeForDecl(self, ast_unit, sl.rest_binding.unwrap(), self.context.type_store.mkSlice(elem_ty, rest_const));
                if (rest_res != .ok) return rest_res;
            }
            return .ok;
        },

        .Path, .Literal => return .ok,
        else => return .ok,
    }
}

/// Check destructuring shape when evaluating an assignment expression `expr` against `value_ty`.
pub fn checkPatternShapeForAssignExpr(
    self: *Checker,
    ast_unit: *ast.Ast,
    expr: ast.ExprId,
    value_ty: types.TypeId,
) PatternShapeCheck {
    const vk = self.typeKind(value_ty);
    switch (ast_unit.kind(expr)) {
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
                    if (vf.name.eq(pf.name.unwrap())) {
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
                if (ast_unit.kind(elems[i]) == .Range) {
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
                if (has_rest) {
                    if (elems.len - 1 > arr.len) return .pattern_shape_mismatch;
                } else {
                    if (elems.len != arr.len) return .pattern_shape_mismatch;
                }
            }

            if (has_rest) {
                // Expect `a .. rest` where end (if any) is an identifier binding the remainder.
                const rr = ast_unit.exprs.get(.Range, elems[rest_index]);
                if (!rr.end.isNone()) {
                    if (ast_unit.kind(rr.end.unwrap()) != .Ident)
                        return .pattern_shape_mismatch;
                }
            }
            return .ok;
        },

        else => return .pattern_shape_mismatch,
    }
}

/// Collect all binding names referenced by pattern `pid` into `list`.
pub fn collectPatternBindings(self: *Checker, ast_unit: *ast.Ast, pid: ast.PatternId, list: *std.ArrayList(ast.StrId)) !void {
    var collector = PatternBindingCollector{
        .gpa = self.gpa,
        .list = list,
    };
    var ctx = check_types.PatternWalkerContext{
        .ctx = @ptrCast(@alignCast(&collector)),
        .onExpr = null,
        .onBinding = patternBindingCollectorOnBinding,
        .onChildType = null,
    };
    try check_types.walkPattern(&ctx, ast_unit, pid, null);
}

const PatternBindingCollector = struct {
    gpa: std.mem.Allocator,
    list: *std.ArrayList(ast.StrId),
};

fn patternBindingCollectorOnBinding(ctx: *void, ast_unit: *ast.Ast, _: ast.PatternId, name: ast.StrId, _: ?types.TypeId) anyerror!void {
    _ = ast_unit;
    const collector: *PatternBindingCollector = @ptrCast(@alignCast(ctx));
    try collector.list.append(collector.gpa, name);
    return;
}

const PatternBindingTypeResolver = struct {
    checker: *Checker,
    target: ast.StrId,
    result: ?types.TypeId = null,
};

fn patternBindingTypeOnBinding(
    ctx: *void,
    ast_unit: *ast.Ast,
    _: ast.PatternId,
    name: ast.StrId,
    value_ty: ?types.TypeId,
) anyerror!void {
    _ = ast_unit;
    if (value_ty == null) return;
    const resolver: *PatternBindingTypeResolver = @ptrCast(@alignCast(ctx));
    if (name.eq(resolver.target)) resolver.result = value_ty;
}

fn patternBindingTypeResolveStructField(self: *Checker, ty: types.TypeId, field_name: ast.StrId) ?types.TypeId {
    const st = self.context.type_store.get(.Struct, ty);
    const fields = self.context.type_store.field_pool.slice(st.fields);
    for (fields) |fid| {
        const tf = self.context.type_store.Field.get(fid);
        if (tf.name.eq(field_name)) return tf.ty;
    }
    return null;
}

fn patternBindingTypeResolveElementType(self: *Checker, ty: types.TypeId) ?types.TypeId {
    return switch (self.typeKind(ty)) {
        .Array => self.context.type_store.get(.Array, ty).elem,
        .Slice => self.context.type_store.get(.Slice, ty).elem,
        .DynArray => self.context.type_store.get(.DynArray, ty).elem,
        else => null,
    };
}

fn patternBindingTypeResolveVariantPayload(self: *Checker, ty: types.TypeId, case_name: ast.StrId) ?types.TypeId {
    if (case_name.eq(ast.StrId.fromRaw(0))) return null;
    return findCasePayload(self, ty, case_name);
}

fn patternBindingTypeChildType(
    ctx: *void,
    _ast_unit: *ast.Ast,
    _parent_pid: ast.PatternId,
    parent_ty: ?types.TypeId,
    _child_pid: ast.PatternId,
    desc: check_types.PatternChildDesc,
) ?types.TypeId {
    const resolver: *PatternBindingTypeResolver = @ptrCast(@alignCast(ctx));
    _ = _ast_unit;
    _ = _parent_pid;
    _ = _child_pid;
    if (parent_ty == null) return null;
    const context_checker = resolver.checker;
    const ty = parent_ty.?;
    const pk = context_checker.typeKind(ty);

    return switch (desc) {
        .TupleElem => {
            if (pk != .Tuple) return null;
            const tp = context_checker.context.type_store.get(.Tuple, ty);
            const elems = context_checker.context.type_store.type_pool.slice(tp.elems);
            if (desc.TupleElem >= elems.len) return null;
            return elems[desc.TupleElem];
        },
        .StructField => if (pk != .Struct) null else patternBindingTypeResolveStructField(context_checker, ty, desc.StructField),
        .VariantTupleElem => {
            if (pk != .Variant and pk != .Error) return null;
            const pay = patternBindingTypeResolveVariantPayload(context_checker, ty, desc.VariantTupleElem.case_name) orelse return null;
            const pay_pk = context_checker.typeKind(pay);
            if (pay_pk == .Tuple) {
                const tp = context_checker.context.type_store.get(.Tuple, pay);
                const tys = context_checker.context.type_store.type_pool.slice(tp.elems);
                if (desc.VariantTupleElem.index >= tys.len) return null;
                return tys[desc.VariantTupleElem.index];
            } else {
                if (desc.VariantTupleElem.index == 0) return pay else return null;
            }
        },
        .VariantStructField => {
            if (pk == .Struct) {
                return patternBindingTypeResolveStructField(context_checker, ty, desc.VariantStructField.field_name);
            } else if (pk == .Variant or pk == .Error) {
                const pay = patternBindingTypeResolveVariantPayload(context_checker, ty, desc.VariantStructField.case_name) orelse return null;
                if (context_checker.typeKind(pay) != .Struct) return null;
                return patternBindingTypeResolveStructField(context_checker, pay, desc.VariantStructField.field_name);
            } else return null;
        },
        .SliceElem => patternBindingTypeResolveElementType(context_checker, ty),
        .SliceRest => {
            const elem = patternBindingTypeResolveElementType(context_checker, ty) orelse return null;
            const rest_const = if (pk == .Slice) context_checker.context.type_store.get(.Slice, ty).is_const else false;
            return context_checker.context.type_store.mkSlice(elem, rest_const);
        },
        .OrAlt, .AtPattern => parent_ty,
    };
}

/// Return the inferred type for binding `name` within pattern `pid`, if any.
pub fn bindingTypeInPattern(
    self: *Checker,
    ast_unit: *ast.Ast,
    pid: ast.PatternId,
    name: ast.StrId,
    value_ty: types.TypeId,
) ?types.TypeId {
    var resolver = PatternBindingTypeResolver{
        .checker = self,
        .target = name,
        .result = null,
    };
    var walker_ctx = check_types.PatternWalkerContext{
        .ctx = @ptrCast(@alignCast(&resolver)),
        .onExpr = null,
        .onBinding = patternBindingTypeOnBinding,
        .onChildType = patternBindingTypeChildType,
    };
    check_types.walkPattern(&walker_ctx, ast_unit, pid, value_ty) catch unreachable;
    return resolver.result;
}
