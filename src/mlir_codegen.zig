const std = @import("std");
const ast = @import("ast.zig");

const c = @cImport({
    @cInclude("mlir-c/IR.h");
    @cInclude("mlir-c/BuiltinTypes.h");
    @cInclude("mlir-c/BuiltinAttributes.h");
    @cInclude("mlir-c/RegisterEverything.h");
    @cInclude("mlir-c/Pass.h");
    @cInclude("mlir-c/ExecutionEngine.h");
});

// Simple MLIR emitter using the C API for a tiny subset:
// - Creates a module
// - Emits a single func.func @main() with an empty body and a return
// This is sufficient to validate end-to-end lowering for examples/hello.sr

pub fn emitModule(program: *const ast.Unit, out_path: ?[]const u8) !void {
    _ = out_path; // currently unused; dump to stdout
    const ctx = c.mlirContextCreate();
    defer c.mlirContextDestroy(ctx);
    // Register everything and append to context
    const registry = c.mlirDialectRegistryCreate();
    defer c.mlirDialectRegistryDestroy(registry);
    c.mlirRegisterAllDialects(registry);
    c.mlirContextAppendDialectRegistry(ctx, registry);
    c.mlirRegisterAllPasses();
    c.mlirRegisterAllLLVMTranslations(ctx);

    const loc = c.mlirLocationUnknownGet(ctx);
    const mod = c.mlirModuleCreateEmpty(loc);
    defer c.mlirOperationDestroy(c.mlirModuleGetOperation(mod));

    // Prepare a global string for hello if needed
    const str_sym = "str0";
    const hello = "Hello, world!";

    // Build memref type memref<Nxi8>
    const i8_ty = c.mlirIntegerTypeGet(ctx, 8);
    var shape: [1]i64 = .{ @intCast(hello.len) };
    const mr_ty = c.mlirMemRefTypeContiguousGet(i8_ty, 1, &shape, c.mlirAttributeGetNull());

    // Emit a module-scope memref.global for the string
    try emitGlobalString(ctx, mod, str_sym, mr_ty, hello);

    // Declare an external print function symbol: @print(memref<13xi8>) -> ()
    // We'll refine types later; for now, match the exact memref length.
    const print_name = "print";

    // Try to find a top-level decl bound to name "main" and a function literal
    var found_main = false;
    for (program.decls.items) |decl| {
        if (decl.binding) |pat| {
            if (pat.* == .Binding and std.mem.eql(u8, pat.Binding.name, "main")) {
                if (decl.value.* == .FunctionLit) {
                    try emitPrintDecl(ctx, mod, print_name, mr_ty);
                    try emitFunction(ctx, mod, "main", &decl.value.FunctionLit, str_sym, mr_ty, print_name);
                    found_main = true;
                    break;
                }
            }
        }
    }

    if (!found_main) {
        // Still print an empty module for sanity
        // no-op
    }

    // Dump to stdout for visibility (file printing omitted to keep link deps minimal)
    c.mlirOperationDump(c.mlirModuleGetOperation(mod));
}

fn emitFunction(ctx: c.MlirContext, mod: c.MlirModule, name: []const u8, fnc: *const ast.FunctionLit, str_sym: []const u8, str_ty: c.MlirType, print_sym: []const u8) !void {
    const loc = c.mlirLocationUnknownGet(ctx);

    // Build func operation state
    var state = c.mlirOperationStateGet(c.mlirStringRefCreateFromCString("func.func"), loc);

    // Symbol name attribute: @name
    const sym_name_key = c.mlirIdentifierGet(ctx, c.mlirStringRefCreateFromCString("sym_name"));
    const sym_name_val = c.mlirStringAttrGet(ctx, c.mlirStringRefCreate(name.ptr, name.len));
    const sym_attr = c.mlirNamedAttributeGet(sym_name_key, sym_name_val);

    // Function type: () -> ()
    var dummy: [1]c.MlirType = undefined;
    const fn_ty = c.mlirFunctionTypeGet(
        ctx,
        0,
        @as([*c]const c.MlirType, @ptrCast(&dummy)),
        0,
        @as([*c]const c.MlirType, @ptrCast(&dummy)),
    );
    const fn_type_key = c.mlirIdentifierGet(ctx, c.mlirStringRefCreateFromCString("function_type"));
    const fn_type_val = c.mlirTypeAttrGet(fn_ty);
    const type_attr = c.mlirNamedAttributeGet(fn_type_key, fn_type_val);

    var attrs = [_]c.MlirNamedAttribute{ sym_attr, type_attr };
    c.mlirOperationStateAddAttributes(&state, attrs.len, &attrs);

    // Create region with one block and a return op
    var region = c.mlirRegionCreate();
    const block = c.mlirBlockCreate(0, null, null);
    c.mlirRegionAppendOwnedBlock(region, block);

    // Very small subset lowering: detect calls to print("...") and emit a const + func.call
    if (fnc.body) |body| {
        for (body.items.items) |stmt| {
            if (stmt == .Expr) {
                const e = &stmt.Expr;
                if (e.* == .PostfixCall) {
                    const call = e.PostfixCall;
                    if (call.callee.* == .Identifier and std.mem.eql(u8, call.callee.Identifier.name, "print")) {
                        if (call.args.items.len == 1 and call.args.items[0].* == .StringLit) {
                            // get the memref from the global and pass to print
                            const str_val = try emitGetGlobal(ctx, block, str_sym, str_ty);
                            try emitCallOp1(ctx, block, print_sym, str_val, str_ty);
                        }
                    }
                }
            }
        }
    }

    // func.return
    var ret_state = c.mlirOperationStateGet(c.mlirStringRefCreateFromCString("func.return"), loc);
    const ret_op = c.mlirOperationCreate(&ret_state);
    c.mlirBlockAppendOwnedOperation(block, ret_op);

    // Attach region to the function op
    c.mlirOperationStateAddOwnedRegions(&state, 1, &region);
    const func_op = c.mlirOperationCreate(&state);

    // Append function op to module body
    const body_block = c.mlirModuleGetBody(mod);
    c.mlirBlockAppendOwnedOperation(body_block, func_op);
}

fn emitCallOp1(ctx: c.MlirContext, block: c.MlirBlock, callee: []const u8, arg0: c.MlirValue, _: c.MlirType) !void {
    const loc = c.mlirLocationUnknownGet(ctx);
    var st = c.mlirOperationStateGet(c.mlirStringRefCreateFromCString("func.call"), loc);
    const callee_ident = c.mlirIdentifierGet(ctx, c.mlirStringRefCreateFromCString("callee"));
    const callee_attr = c.mlirFlatSymbolRefAttrGet(ctx, c.mlirStringRefCreate(callee.ptr, callee.len));
    const named = c.mlirNamedAttributeGet(callee_ident, callee_attr);
    c.mlirOperationStateAddAttributes(&st, 1, &named);
    var operands = [_]c.MlirValue{ arg0 };
    c.mlirOperationStateAddOperands(&st, operands.len, &operands);
    // Add result/operand types to call (prints nicer with types)
    // operands types captured in function type; no need to add result types here
    // func.call has results == 0; no need to add results
    const op = c.mlirOperationCreate(&st);
    c.mlirBlockAppendOwnedOperation(block, op);
}

fn emitGlobalString(ctx: c.MlirContext, mod: c.MlirModule, sym: []const u8, ty: c.MlirType, s: []const u8) !void {
    const loc = c.mlirLocationUnknownGet(ctx);
    var st = c.mlirOperationStateGet(c.mlirStringRefCreateFromCString("memref.global"), loc);
    const sym_name = c.mlirIdentifierGet(ctx, c.mlirStringRefCreateFromCString("sym_name"));
    const sym_val = c.mlirStringAttrGet(ctx, c.mlirStringRefCreate(sym.ptr, sym.len));
    const a_sym = c.mlirNamedAttributeGet(sym_name, sym_val);

    const type_key = c.mlirIdentifierGet(ctx, c.mlirStringRefCreateFromCString("type"));
    const type_val = c.mlirTypeAttrGet(ty);
    const a_type = c.mlirNamedAttributeGet(type_key, type_val);

    const val_key = c.mlirIdentifierGet(ctx, c.mlirStringRefCreateFromCString("value"));
    const str_attr = c.mlirStringAttrGet(ctx, c.mlirStringRefCreate(s.ptr, s.len));
    const a_val = c.mlirNamedAttributeGet(val_key, str_attr);

    const const_key = c.mlirIdentifierGet(ctx, c.mlirStringRefCreateFromCString("constant"));
    const const_val = c.mlirUnitAttrGet(ctx);
    const a_const = c.mlirNamedAttributeGet(const_key, const_val);

    var attrs = [_]c.MlirNamedAttribute{ a_sym, a_type, a_val, a_const };
    c.mlirOperationStateAddAttributes(&st, attrs.len, &attrs);
    const op = c.mlirOperationCreate(&st);
    const body_block = c.mlirModuleGetBody(mod);
    c.mlirBlockAppendOwnedOperation(body_block, op);
}

fn emitGetGlobal(ctx: c.MlirContext, block: c.MlirBlock, sym: []const u8, ty: c.MlirType) !c.MlirValue {
    const loc = c.mlirLocationUnknownGet(ctx);
    var st = c.mlirOperationStateGet(c.mlirStringRefCreateFromCString("memref.get_global"), loc);
    const name_key = c.mlirIdentifierGet(ctx, c.mlirStringRefCreateFromCString("name"));
    const name_attr = c.mlirFlatSymbolRefAttrGet(ctx, c.mlirStringRefCreate(sym.ptr, sym.len));
    const a_name = c.mlirNamedAttributeGet(name_key, name_attr);
    c.mlirOperationStateAddAttributes(&st, 1, &a_name);
    var results = [_]c.MlirType{ ty };
    c.mlirOperationStateAddResults(&st, results.len, &results);
    const op = c.mlirOperationCreate(&st);
    c.mlirBlockAppendOwnedOperation(block, op);
    return c.mlirOperationGetResult(op, 0);
}

fn emitPrintDecl(ctx: c.MlirContext, mod: c.MlirModule, name: []const u8, arg_ty: c.MlirType) !void {
    const loc = c.mlirLocationUnknownGet(ctx);
    var st = c.mlirOperationStateGet(c.mlirStringRefCreateFromCString("func.func"), loc);
    const sym_name_key = c.mlirIdentifierGet(ctx, c.mlirStringRefCreateFromCString("sym_name"));
    const sym_name_val = c.mlirStringAttrGet(ctx, c.mlirStringRefCreate(name.ptr, name.len));
    const a_sym = c.mlirNamedAttributeGet(sym_name_key, sym_name_val);
    // build function type (arg_ty) -> ()
    var inputs = [_]c.MlirType{ arg_ty };
    var dummy: [1]c.MlirType = undefined;
    const fn_ty = c.mlirFunctionTypeGet(ctx, 1, @as([*c]const c.MlirType, @ptrCast(&inputs)), 0, @as([*c]const c.MlirType, @ptrCast(&dummy)));
    const fn_type_key = c.mlirIdentifierGet(ctx, c.mlirStringRefCreateFromCString("function_type"));
    const fn_type_val = c.mlirTypeAttrGet(fn_ty);
    const a_type = c.mlirNamedAttributeGet(fn_type_key, fn_type_val);
    var attrs = [_]c.MlirNamedAttribute{ a_sym, a_type };
    c.mlirOperationStateAddAttributes(&st, attrs.len, &attrs);
    // No region means declaration only
    const op = c.mlirOperationCreate(&st);
    const body_block = c.mlirModuleGetBody(mod);
    c.mlirBlockAppendOwnedOperation(body_block, op);
}
