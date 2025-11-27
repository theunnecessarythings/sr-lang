const std = @import("std");
const ast = @import("ast.zig");
const compile = @import("compile.zig");

/// Utility module that resolves function declarations for call expressions.
pub const CallResolution = @This();

/// Captures the AST and declaration id that match a call target.
pub const FunctionDeclContext = struct {
    /// AST container that owns the resolved declaration.
    ast: *ast.Ast,
    /// Identifier of the declaration that matches the call.
    decl_id: ast.DeclId,
};

/// Resolve the function declaration corresponding to `callee_expr` and `callee_name`.
/// `caller_ast` provides the current AST context while `ctx` supplies imports/packages.
pub fn findFunctionDeclForCall(
    ctx: *compile.Context,
    caller_ast: *ast.Ast,
    callee_expr: ast.ExprId,
    callee_name: ast.StrId,
) ?FunctionDeclContext {
    // Resolve the function declaration context for the call expression `callee_expr`.
    // Looks for a top-level declaration or follows a field access via imports.
    if (findTopLevelDeclByName(caller_ast, callee_name)) |decl_id| {
        const decl = caller_ast.exprs.Decl.get(decl_id);
        if (caller_ast.kind(decl.value) != .Import) {
            return FunctionDeclContext{ .ast = caller_ast, .decl_id = decl_id };
        }
    }

    if (caller_ast.kind(callee_expr) != .FieldAccess) return null;

    const fr = caller_ast.exprs.get(.FieldAccess, callee_expr);

    return findFunctionDeclFromFieldAccess(ctx, caller_ast, fr, callee_name);
}

/// Locate the declaration id for `name` within AST `a`, preferring exported symbols.
pub fn findDeclIdByName(a: *ast.Ast, name: ast.StrId) ?ast.DeclId {
    if (a.type_info.getExport(name)) |ex| {
        return ex.decl_id;
    }
    const decls = a.exprs.decl_pool.slice(a.unit.decls);
    for (decls) |did| {
        const d = a.exprs.Decl.get(did);
        if (d.pattern.isNone()) continue;
        const pat = d.pattern.unwrap();
        if (bindingNameOfPattern(a, pat)) |nm| {
            if (nm.eq(name)) {
                return did;
            }
        }
    }
    return null;
}

/// Return the identifier name bound by pattern `pid`, if it is a simple binding.
fn bindingNameOfPattern(ast_unit: *ast.Ast, pid: ast.PatternId) ?ast.StrId {
    return switch (ast_unit.kind(pid)) {
        .Binding => ast_unit.pats.get(.Binding, pid).name,
        else => null,
    };
}

/// Find a top-level declaration whose bound pattern contains `name`.
pub fn findTopLevelDeclByName(a: *ast.Ast, name: ast.StrId) ?ast.DeclId {
    const target = a.exprs.strs.get(name);
    return findTopLevelDeclByNameSlice(a, target);
}

/// Iterate decls to see if `target` is bound by a declaration pattern.
fn findTopLevelDeclByNameSlice(a: *ast.Ast, target: []const u8) ?ast.DeclId {
    const decls = a.exprs.decl_pool.slice(a.unit.decls);
    var i: usize = 0;
    while (i < decls.len) : (i += 1) {
        const d = a.exprs.Decl.get(decls[i]);
        if (d.pattern.isNone()) continue;
        const pid = d.pattern.unwrap();
        if (patternContainsNameStr(a, pid, target)) return decls[i];
    }
    return null;
}

/// Recursively check whether pattern `pid` binds the identifier spelled by `target`.
fn patternContainsNameStr(a: *ast.Ast, pid: ast.PatternId, target: []const u8) bool {
    return switch (a.kind(pid)) {
        .Binding => {
            const nm = a.pats.get(.Binding, pid).name;
            return std.mem.eql(u8, a.exprs.strs.get(nm), target);
        },
        .Tuple => {
            const row = a.pats.get(.Tuple, pid);
            const elems = a.pats.pat_pool.slice(row.elems);
            for (elems) |eid| if (patternContainsNameStr(a, eid, target)) return true;
            return false;
        },
        .Struct => {
            const row = a.pats.get(.Struct, pid);
            const fields = a.pats.field_pool.slice(row.fields);
            for (fields) |fid| {
                const frow = a.pats.StructField.get(fid);
                if (patternContainsNameStr(a, frow.pattern, target)) return true;
            }
            return false;
        },
        .VariantTuple => {
            const row = a.pats.get(.VariantTuple, pid);
            const elems = a.pats.pat_pool.slice(row.elems);
            for (elems) |eid| if (patternContainsNameStr(a, eid, target)) return true;
            return false;
        },
        .VariantStruct => {
            const row = a.pats.get(.VariantStruct, pid);
            const fields = a.pats.field_pool.slice(row.fields);
            for (fields) |fid| {
                const frow = a.pats.StructField.get(fid);
                if (patternContainsNameStr(a, frow.pattern, target)) return true;
            }
            return false;
        },
        .Slice => {
            const row = a.pats.get(.Slice, pid);
            const elems = a.pats.pat_pool.slice(row.elems);
            for (elems) |eid| if (patternContainsNameStr(a, eid, target)) return true;
            if (!row.rest_binding.isNone()) {
                return patternContainsNameStr(a, row.rest_binding.unwrap(), target);
            }
            return false;
        },
        .Or => {
            const row = a.pats.get(.Or, pid);
            const alts = a.pats.pat_pool.slice(row.alts);
            for (alts) |aid| if (patternContainsNameStr(a, aid, target)) return true;
            return false;
        },
        .At => {
            const row = a.pats.get(.At, pid);
            const binder = a.exprs.strs.get(row.binder);
            if (std.mem.eql(u8, binder, target)) return true;
            return patternContainsNameStr(a, row.pattern, target);
        },
        else => false,
    };
}

/// Return the declaration id for an import whose alias `name` matches, if any.
pub fn findTopLevelImportByName(a: *ast.Ast, name: ast.StrId) ?ast.DeclId {
    const did = findTopLevelDeclByName(a, name) orelse return null;
    const d = a.exprs.Decl.get(did);
    return if (a.kind(d.value) == .Import) did else null;
}

/// Look up a function declaration when the callee is a field access (`A.B()`).
pub fn findFunctionDeclFromFieldAccess(
    ctx: *compile.Context,
    caller_ast: *ast.Ast,
    fr: ast.Rows.FieldAccess,
    callee_name: ast.StrId,
) ?FunctionDeclContext {
    if (caller_ast.kind(fr.parent) == .Import) {
        const ir = caller_ast.exprs.get(.Import, fr.parent);
        const path = caller_ast.exprs.strs.get(ir.path);
        var pkg_iter = ctx.compilation_unit.packages.iterator();
        while (pkg_iter.next()) |pkg| {
            if (pkg.value_ptr.sources.get(path)) |unit_ref| {
                if (unit_ref.ast) |a| {
                    if (findDeclIdByName(a, callee_name)) |decl_id| {
                        return FunctionDeclContext{ .ast = a, .decl_id = decl_id };
                    }
                }
                break;
            }
        }
        return null;
    }

    if (caller_ast.kind(fr.parent) == .Ident) {
        const parent_ident = caller_ast.exprs.get(.Ident, fr.parent);
        if (findTopLevelImportByName(caller_ast, parent_ident.name)) |import_decl_id| {
            const import_decl = caller_ast.exprs.Decl.get(import_decl_id);
            const ir = caller_ast.exprs.get(.Import, import_decl.value);
            const path = caller_ast.exprs.strs.get(ir.path);
            var pkg_iter2 = ctx.compilation_unit.packages.iterator();
            while (pkg_iter2.next()) |pkg| {
                if (pkg.value_ptr.sources.get(path)) |unit_ref| {
                    if (unit_ref.ast) |a| {
                        if (findDeclIdByName(a, callee_name)) |decl_id| {
                            return FunctionDeclContext{ .ast = a, .decl_id = decl_id };
                        }
                    }
                    break;
                }
            }
        }
    }

    return null;
}
