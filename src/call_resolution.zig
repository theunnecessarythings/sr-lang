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
pub fn findFunctionDeclForCall(
    ctx: *compile.Context,
    caller_ast: *ast.Ast,
    callee_expr: ast.ExprId,
    callee_name: ast.StrId,
) ?FunctionDeclContext {
    // 1. Try Local Top-Level Declaration
    if (findDeclId(caller_ast, callee_name)) |decl_id| {
        const decl = caller_ast.exprs.Decl.get(decl_id);
        if (caller_ast.kind(decl.value) != .Import) {
            return FunctionDeclContext{ .ast = caller_ast, .decl_id = decl_id };
        }
    }

    // 2. Try Field Access on Import (e.g. `std.debug.print`)
    if (caller_ast.kind(callee_expr) == .FieldAccess) {
        const fr = caller_ast.exprs.get(.FieldAccess, callee_expr);
        return findFunctionDeclFromFieldAccess(ctx, caller_ast, fr, callee_name);
    }

    return null;
}

/// Locate the declaration id for `name` within AST `a`, utilizing fast ID checks.
pub fn findDeclId(a: *ast.Ast, name: ast.StrId) ?ast.DeclId {
    // Fast path: Check explicit exports map
    if (a.type_info.getExport(name)) |ex| return ex.decl_id;

    // Slow path: Linear scan of top-level decls (O(N))
    // Optimization: Compare StrIds (integer) instead of string slices.
    const decls = a.exprs.decl_pool.slice(a.unit.decls);
    for (decls) |did| {
        const d = a.exprs.Decl.get(did);
        if (d.pattern.isNone()) continue;
        if (patternContainsName(a, d.pattern.unwrap(), name)) return did;
    }
    return null;
}

/// Recursively check whether pattern `pid` binds the identifier `target_id`.
fn patternContainsName(a: *ast.Ast, pid: ast.PatternId, target_id: ast.StrId) bool {
    switch (a.kind(pid)) {
        .Binding => return a.pats.get(.Binding, pid).name.eq(target_id),
        .Tuple => {
            const elems = a.pats.pat_pool.slice(a.pats.get(.Tuple, pid).elems);
            for (elems) |eid| if (patternContainsName(a, eid, target_id)) return true;
        },
        .Struct => {
            const fields = a.pats.field_pool.slice(a.pats.get(.Struct, pid).fields);
            for (fields) |fid| if (patternContainsName(a, a.pats.StructField.get(fid).pattern, target_id)) return true;
        },
        // Flattened recursion for Variants/Slices/etc to reduce stack depth
        .VariantTuple => {
            const elems = a.pats.pat_pool.slice(a.pats.get(.VariantTuple, pid).elems);
            for (elems) |eid| if (patternContainsName(a, eid, target_id)) return true;
        },
        .VariantStruct => {
            const fields = a.pats.field_pool.slice(a.pats.get(.VariantStruct, pid).fields);
            for (fields) |fid| if (patternContainsName(a, a.pats.StructField.get(fid).pattern, target_id)) return true;
        },
        .Slice => {
            const row = a.pats.get(.Slice, pid);
            const elems = a.pats.pat_pool.slice(row.elems);
            for (elems) |eid| if (patternContainsName(a, eid, target_id)) return true;
            if (!row.rest_binding.isNone()) return patternContainsName(a, row.rest_binding.unwrap(), target_id);
        },
        .Or => {
            const alts = a.pats.pat_pool.slice(a.pats.get(.Or, pid).alts);
            for (alts) |aid| if (patternContainsName(a, aid, target_id)) return true;
        },
        .At => {
            const row = a.pats.get(.At, pid);
            if (row.binder.eq(target_id)) return true;
            return patternContainsName(a, row.pattern, target_id);
        },
        else => {},
    }
    return false;
}

/// Helper to resolve an import path string to an AST.
fn resolveImportedAst(ctx: *compile.Context, path_str: []const u8) ?*ast.Ast {
    var it = ctx.compilation_unit.packages.iterator();
    while (it.next()) |pkg| {
        if (pkg.value_ptr.sources.get(path_str)) |ref| {
            if (ref.ast) |a| return a;
        }
    }
    return null;
}

/// Look up a function declaration when the callee is a field access (`A.B()`).
pub fn findFunctionDeclFromFieldAccess(
    ctx: *compile.Context,
    caller_ast: *ast.Ast,
    fr: ast.Rows.FieldAccess,
    callee_name: ast.StrId,
) ?FunctionDeclContext {
    var path_str: []const u8 = "";

    // 1. Check if parent is direct @import(...)
    if (caller_ast.kind(fr.parent) == .Import) {
        path_str = caller_ast.exprs.strs.get(caller_ast.exprs.get(.Import, fr.parent).path);
    }
    // 2. Check if parent is Identifier resolving to an Import decl
    else if (caller_ast.kind(fr.parent) == .Ident) {
        const ident_name = caller_ast.exprs.get(.Ident, fr.parent).name;
        if (findDeclId(caller_ast, ident_name)) |decl_id| {
            const decl = caller_ast.exprs.Decl.get(decl_id);
            if (caller_ast.kind(decl.value) == .Import) {
                path_str = caller_ast.exprs.strs.get(caller_ast.exprs.get(.Import, decl.value).path);
            }
        }
    }

    if (path_str.len == 0) return null;

    // Resolve AST from path string
    if (resolveImportedAst(ctx, path_str)) |imported_ast| {
        if (findDeclId(imported_ast, callee_name)) |decl_id| {
            return FunctionDeclContext{ .ast = imported_ast, .decl_id = decl_id };
        }
    }
    return null;
}
