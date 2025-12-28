const std = @import("std");
const Loc = @import("lexer.zig").Token.Loc;
const Tag = @import("lexer.zig").Token.Tag;
const Context = @import("compile.zig").Context;
const BinaryOp = @import("ast.zig").BinaryOp;
const UnaryOp = @import("ast.zig").UnaryOp;
const ast = @import("ast.zig");
const types = @import("types.zig");
const TypeKind = types.TypeKind;

fn oom() noreturn {
    @branchHint(.cold);
    @panic("OOM");
}

pub const DiagnosticContext = struct {
    type_store: *types.TypeStore,
    str_interner: *types.StringInterner,
    gpa: std.mem.Allocator,
};

pub const Severity = enum { err, warning, note };

// --- Payload Tagging Optimization ---
const TagCount = std.meta.fields(Tag).len;
const BinOpCount = std.meta.fields(BinaryOp).len;
const UnOpCount = std.meta.fields(UnaryOp).len;
const TypeKindCount = std.meta.fields(TypeKind).len;

fn payloadTag() type {
    const total_fields = TagCount + BinOpCount + UnOpCount + TypeKindCount;
    return @Type(.{
        .@"enum" = .{
            .tag_type = std.math.IntFittingRange(0, total_fields - 1),
            .fields = &generateFields(total_fields),
            .decls = &.{},
            .is_exhaustive = true,
        },
    });
}

fn generateFields(comptime N: usize) [N]std.builtin.Type.EnumField {
    var fields: [N]std.builtin.Type.EnumField = undefined;
    const all_source_fields = std.meta.fields(Tag) ++ std.meta.fields(BinaryOp) ++ std.meta.fields(UnaryOp) ++ std.meta.fields(TypeKind);
    inline for (all_source_fields, 0..) |f, i| {
        fields[i] = .{ .name = f.name, .value = i };
    }
    return fields;
}

const PayloadTag = payloadTag();

fn convertToPayloadTag(value: anytype) PayloadTag {
    const val = @intFromEnum(value);
    switch (@TypeOf(value)) {
        Tag => return @enumFromInt(val),
        BinaryOp => return @enumFromInt(val + TagCount),
        UnaryOp => return @enumFromInt(val + TagCount + BinOpCount),
        TypeKind => return @enumFromInt(val + TagCount + BinOpCount + UnOpCount),
        else => @compileError("Unsupported type for PayloadTag"),
    }
}

const MessagePayload = union(enum) {
    none,
    string: []const u8,
    one: struct { a: PayloadTag },
    two: struct { a: PayloadTag, b: PayloadTag },
    three: struct { a: PayloadTag, b: PayloadTag, c: PayloadTag },
    str_id: ast.StrId,
    type_id: types.TypeId,
    two_type_ids: struct { a: types.TypeId, b: types.TypeId },
    integer: i64,
    two_integers: struct { a: i64, b: i64 },
    string_and_type: struct { s: ast.StrId, t: types.TypeId },
    two_strings_and_type: struct { s1: ast.StrId, s2: ast.StrId, t: types.TypeId },
};

pub const DiagnosticCode = enum {
    unexpected_token,
    unexpected_closing_delimiter,
    mismatched_closing_delimiter,
    expected_identifier,
    expected_expression_after_operator,
    expected_type_in_declaration,
    expected_field_name_or_index,
    expected_closure_param_separator,
    expected_loop_after_label,
    unexpected_postfix_operator,
    unexpected_token_in_expression,
    invalid_float_literal,
    invalid_integer_literal,
    invalid_imaginary_literal,
    expected_attribute_name,
    expected_map_type_or_literal_continuation,
    expected_array_like_continuation,
    expected_attribute_value,
    expected_extern_async_function,
    expected_extern_declaration,
    expected_parameter_type_or_end,
    invalid_import_operand,
    import_not_found,
    invalid_package_name,
    token_cannot_start_pattern,
    unexpected_token_in_pattern,
    invalid_binding_name_in_at_pattern,
    underscore_not_const_in_range_pattern,
    left_side_not_const_like_in_range_pattern,
    descending_range_pattern,
    string_equality_in_match_not_supported,
    pattern_shape_mismatch,
    pattern_type_mismatch,
    or_pattern_binding_mismatch,
    or_pattern_binding_type_mismatch,
    empty_path_pattern,
    unknown_type_in_path,
    unsupported_pattern_type,
    tensor_missing_arguments,
    tensor_missing_element_type,
    tensor_dimension_not_integer_literal,
    tensor_rank_exceeds_limit,
    tensor_rank_mismatch,
    tensor_dimension_mismatch,
    tensor_element_type_mismatch,
    simd_lanes_not_integer_literal,
    simd_invalid_element_type,
    array_size_not_integer_literal,
    array_length_mismatch,
    heterogeneous_array_elements,
    cannot_infer_type_from_empty_array,
    cannot_infer_type_from_null,
    cannot_infer_range_type,
    could_not_resolve_type,
    map_wrong_key_type,
    map_mixed_key_types,
    map_mixed_value_types,
    noreturn_not_storable,
    type_value_mismatch,
    type_annotation_mismatch,
    mlir_block_not_a_type,
    cast_target_not_type,
    invalid_cast,
    invalid_checked_cast,
    invalid_bitcast,
    bitcast_non_numeric_or_pointer,
    bitcast_target_non_numeric_or_pointer,
    numeric_cast_on_non_numeric,
    bitcast_size_unknown,
    invalid_binary_op_operands,
    invalid_unary_op_operand,
    division_by_zero,
    in_operator_not_supported,
    non_boolean_condition,
    if_expression_requires_else,
    if_branch_type_mismatch,
    range_type_mismatch,
    range_requires_integer_operands,
    while_expression_not_value,
    non_iterable_in_for,
    tuple_arity_mismatch,
    struct_pattern_field_mismatch,
    variant_payload_mismatch,
    non_exhaustive_match,
    overlapping_match_arm,
    unreachable_match_arm,
    loop_break_value_type_conflict,
    assignment_type_mismatch,
    unreachable_code_after_break,
    await_non_async,
    await_type_mismatch,
    await_outside_async_context,
    field_access_on_non_aggregate,
    invalid_struct_field_index,
    non_integer_index,
    await_on_non_future,
    not_indexable,
    invalid_index_type,
    identifier_not_type,
    expected_array_type,
    expected_tensor_type,
    expected_map_type,
    expected_struct_type,
    expected_enum_type,
    expected_tuple_type,
    expected_pointer_type,
    expected_integer_type,
    expected_float_type,
    method_requires_function_value,
    method_requires_self_parameter,
    method_self_must_be_binding,
    method_self_requires_type,
    method_self_type_mismatch,
    method_owner_not_struct,
    method_invalid_owner_path,
    duplicate_method_on_type,
    method_receiver_requires_pointer,
    method_receiver_requires_value,
    method_receiver_not_addressable,
    checker_comptime_not_executed,
    checker_code_block_not_executed,
    insert_requires_code,
    insert_requires_decl,
    code_splice_unknown_identifier,
    code_splice_requires_code,
    code_splice_requires_expr,
    code_splice_requires_type,
    code_splice_unsupported,
    return_outside_function,
    return_value_in_void_function,
    missing_return_value,
    return_type_mismatch,
    break_outside_loop,
    continue_outside_loop,
    defer_outside_function,
    errdefer_outside_function,
    errdefer_in_non_error_function,
    nested_function_not_allowed,
    duplicate_field,
    duplicate_enum_field,
    enum_discriminant_not_integer,
    duplicate_variant,
    duplicate_error_variant,
    tuple_index_out_of_bounds,
    struct_field_count_mismatch,
    struct_field_name_mismatch,
    struct_field_type_mismatch,
    struct_missing_field,
    unknown_struct_field,
    unknown_module_field,
    unknown_tuple_field,
    expected_pattern_on_decl_lhs,
    missing_field_name_in_struct_literal,
    unknown_enum_tag,
    unknown_variant_tag,
    enum_tag_type_mismatch,
    variant_payload_arity_mismatch,
    variant_payload_field_mismatch,
    variant_payload_field_type_mismatch,
    variant_payload_field_requires_non_null,
    union_literal_multiple_fields,
    union_field_type_mismatch,
    unknown_union_field,
    union_empty_literal,
    union_field_requires_non_null,
    unknown_error_tag,
    error_assigned_to_non_error_union,
    invalid_use_of_orelse_on_non_optional,
    orelse_type_mismatch,
    catch_on_non_error,
    catch_handler_type_mismatch,
    invalid_optional_unwrap_target,
    error_propagation_on_non_error,
    error_propagation_mismatched_function_result,
    purity_violation,
    struct_field_requires_non_null,
    assign_null_to_non_optional,
    pointer_type_mismatch,
    deref_non_pointer,
    pointer_constness_violation,
    slice_constness_violation,
    invalid_any_type_annotation,
    wrong_arity_in_call,
    argument_type_mismatch,
    call_non_callable,
    argument_count_mismatch,
    null_to_non_optional_param,
    undefined_identifier,
    unknown_function,
    unexpected_after_expression,
    expected_comma_or_rparen,
    expected_colon_or_comma_in_param,
    mlir_verification_failed,
    mlir_parse_error,
    mlir_splice_unknown_identifier,
    mlir_splice_not_comptime,
    mlir_splice_unbound,
    mlir_operation_missing_result_type,
    comptime_type_not_supported,
    package_missing_declaration,
    entry_package_missing,
    entry_package_not_main,
    checker_internal_error,
    tir_lowering_failed,
    tir_variant_tag_not_found,
    tir_codegen_missing_operand,
    import_cycle_detected,
    imports_blocked_by_cycle,
    unused_function,
    unused_param,
    unused_variable,
};

pub fn diagnosticMessageFmt(code: DiagnosticCode) []const u8 {
    return switch (code) {
        .unexpected_token => "expected {s}, found {s}",
        .unexpected_closing_delimiter => "unexpected closing delimiter: {s}",
        .mismatched_closing_delimiter => "mismatched closing delimiter: expected {s}, found {s}",
        .expected_identifier => "expected identifier, found {s}",
        .expected_expression_after_operator => "expected expression after operator {s}",
        .expected_type_in_declaration => "expected '=' or '::' after type in declaration, found {s}",
        .expected_field_name_or_index => "expected identifier or integer after '.', found {s}",
        .expected_closure_param_separator => "expected ',' or '|' after closure parameter, found {s}",
        .expected_loop_after_label => "expected 'for' or 'while' after label, found {s}",
        .unexpected_postfix_operator => "unexpected postfix operator: {s}",
        .unexpected_token_in_expression => "unexpected token in expression: {s}",
        .invalid_float_literal => "invalid float literal: '{s}'",
        .invalid_integer_literal => "invalid integer literal: '{s}'",
        .invalid_imaginary_literal => "invalid imaginary literal: '{s}'",
        .expected_attribute_name => "expected attribute name, found {s}",
        .expected_map_type_or_literal_continuation => "expected ']' or ',' in map type/literal, found {s}",
        .expected_array_like_continuation => "expected ']', ':', or ',' in array-like, found {s}",
        .expected_attribute_value => "expected literal or identifier after '=', found {s}",
        .expected_extern_async_function => "expected 'proc' or 'fn' after 'extern async', found {s}",
        .expected_extern_declaration => "expected 'proc', 'fn', or a type after 'extern', found {s}",
        .expected_parameter_type_or_end => "expected ':', ',', or ')' after parameter, found {s}",
        .invalid_import_operand => "invalid import operand; expected string-like path, found {s}",
        .import_not_found => "import not found: '{s}'",
        .invalid_package_name => "invalid package name: '{s}'",
        .token_cannot_start_pattern => "this token cannot start a pattern: {s}",
        .unexpected_token_in_pattern => "unexpected token in pattern: {s}",
        .invalid_binding_name_in_at_pattern => "only simple identifier paths can be used as binding names in '@' patterns; found {s}",
        .underscore_not_const_in_range_pattern => "'_' is not valid as a constant in a range pattern",
        .left_side_not_const_like_in_range_pattern => "left side of a range pattern must be const-like",
        .descending_range_pattern => "descending range pattern: {s}..{s}",
        .string_equality_in_match_not_supported => "string equality in 'match' is not supported",
        .pattern_shape_mismatch => "pattern shape mismatch: {s}",
        .pattern_type_mismatch => "pattern type mismatch: expected {s}, found {s}",
        .or_pattern_binding_mismatch => "bindings in 'or' pattern arms do not match",
        .or_pattern_binding_type_mismatch => "bindings in 'or' pattern arms have mismatched types",
        .empty_path_pattern => "empty path pattern",
        .unknown_type_in_path => "unknown type in path pattern: '{s}'",
        .unsupported_pattern_type => "unsupported pattern type: {s}",
        .tensor_missing_arguments => "expected at least one argument to 'tensor', found none",
        .tensor_missing_element_type => "tensor is missing the element type",
        .tensor_dimension_not_integer_literal => "tensor dimension must be integer literal, found {s}",
        .tensor_rank_exceeds_limit => "tensor rank {d} exceeds maximum of {d}",
        .tensor_rank_mismatch => "tensor rank mismatch: expected {d}, found {d}",
        .tensor_dimension_mismatch => "tensor dimension mismatch: {s}",
        .tensor_element_type_mismatch => "tensor element type mismatch: expected {s}, found {s}",
        .simd_lanes_not_integer_literal => "SIMD lanes must be integer literal, found {s}",
        .simd_invalid_element_type => "invalid SIMD element type: {s}",
        .array_size_not_integer_literal => "array size must be integer literal, found {s}",
        .array_length_mismatch => "array length mismatch: expected {d}, found {d}",
        .heterogeneous_array_elements => "heterogeneous array: expected {s}, found {s}",
        .cannot_infer_type_from_empty_array => "cannot infer type from empty array literal; add a type annotation",
        .cannot_infer_type_from_null => "cannot infer type from 'null' literal; add a type annotation",
        .cannot_infer_range_type => "cannot infer type from range with no start or end value; add a type annotation to at least one side",
        .could_not_resolve_type => "could not resolve type: '{s}'",
        .map_wrong_key_type => "map key type mismatch: expected {s}, found {s}",
        .map_mixed_key_types => "map has mixed key types: {s} and {s}",
        .map_mixed_value_types => "map has mixed value types: {s} and {s}",
        .noreturn_not_storable => "type 'noreturn' cannot be used as a variable or struct field type",
        .type_value_mismatch => "expected a type, found value of type {s}",
        .type_annotation_mismatch => "type mismatch: annotated as {s}, initialized with {s}",
        .cast_target_not_type => "cast target is not a type",
        .invalid_cast => "invalid cast from {s} to {s}",
        .invalid_checked_cast => "checked cast from {s} to {s} cannot succeed",
        .invalid_bitcast => "invalid bitcast from {s} to {s}",
        .bitcast_non_numeric_or_pointer => "bitcast source must be numeric or pointer, found {s}",
        .bitcast_target_non_numeric_or_pointer => "bitcast target must be numeric or pointer, found {s}",
        .numeric_cast_on_non_numeric => "numeric cast applied to non-numeric type: {s}",
        .bitcast_size_unknown => "cannot determine size for bitcast",
        .invalid_binary_op_operands => "invalid operands for binary operator '{s}': {s} and {s}",
        .invalid_unary_op_operand => "invalid operand for unary operator '{s}': {s}",
        .division_by_zero => "division by zero",
        .in_operator_not_supported => "'in' operator is not implemented yet",
        .non_boolean_condition => "condition must be bool, found {s}",
        .if_expression_requires_else => "'if' used as an expression must have an 'else' branch",
        .if_branch_type_mismatch => "if branch type mismatch: then returns {s}, else returns {s}",
        .range_type_mismatch => "range type mismatch: start is {s}, end is {s}",
        .range_requires_integer_operands => "range requires integers, found {s} and {s}",
        .while_expression_not_value => "'while' cannot be used as a value (no resulting expression)",
        .non_iterable_in_for => "value is not iterable: {s}",
        .tuple_arity_mismatch => "tuple arity mismatch: pattern has {d} elements, value has {d}",
        .struct_pattern_field_mismatch => "struct pattern field mismatch: {s}",
        .variant_payload_mismatch => "variant payload mismatch: {s}",
        .non_exhaustive_match => "non-exhaustive match; missing: {s}",
        .overlapping_match_arm => "overlapping or duplicate match arm",
        .unreachable_match_arm => "unreachable match arm (covered by previous arms)",
        .loop_break_value_type_conflict => "loop break type conflict: {s} vs {s}",
        .assignment_type_mismatch => "assignment type mismatch: variable is {s}, value is {s}",
        .unreachable_code_after_break => "unreachable code after an unconditional break",
        .await_non_async => "'await' on non-async expression of type {s}",
        .await_type_mismatch => "await type mismatch: expected {s}, found {s}",
        .await_outside_async_context => "'await' used outside of an async context",
        .field_access_on_non_aggregate => "field access on non-aggregate value of type {s}",
        .invalid_struct_field_index => "numeric field access is invalid on a struct; found {s}",
        .not_indexable => "value of type {s} is not indexable",
        .non_integer_index => "array index must be integer, found {s}",
        .await_on_non_future => "cannot 'await' on non-future type {s}",
        .invalid_index_type => "invalid index type: {s}",
        .identifier_not_type => "identifier '{s}' is not a type",
        .expected_array_type => "expected array type, found {s}",
        .expected_tensor_type => "expected tensor type, found {s}",
        .expected_map_type => "expected map type, found {s}",
        .expected_struct_type => "expected struct type, found {s}",
        .expected_enum_type => "expected enum type, found {s}",
        .expected_tuple_type => "expected tuple type, found {s}",
        .expected_pointer_type => "expected pointer type, found {s}",
        .expected_integer_type => "expected integer type, found {s}",
        .expected_float_type => "expected float type, found {s}",
        .method_requires_function_value => "methods must be defined with a function value",
        .method_requires_self_parameter => "methods must declare a 'self' parameter as the first argument",
        .method_self_must_be_binding => "the first parameter of a method must bind to 'self'",
        .method_self_requires_type => "the 'self' parameter of a method requires an explicit type",
        .method_self_type_mismatch => "method 'self' type mismatch: {s} vs {s}",
        .method_owner_not_struct => "methods cannot be declared on type {s}",
        .method_invalid_owner_path => "methods must be declared on a simple struct name",
        .duplicate_method_on_type => "duplicate method '{s}' for this struct",
        .method_receiver_requires_pointer => "method '{s}' requires a pointer receiver",
        .method_receiver_requires_value => "method '{s}' requires a value receiver",
        .method_receiver_not_addressable => "method '{s}' requires an addressable receiver",
        .checker_comptime_not_executed => "checker: comptime not executed; walking only",
        .checker_code_block_not_executed => "checker: code block not executed; walking only",
        .insert_requires_code => "insert expects a Code value",
        .insert_requires_decl => "insert code blocks must contain only declarations",
        .code_splice_unknown_identifier => "unknown splice `{s}`",
        .code_splice_requires_code => "splice `{s}` expects a Code value",
        .code_splice_requires_expr => "splice expects a single expression",
        .code_splice_requires_type => "splice `{s}` expects a type value",
        .code_splice_unsupported => "splice value cannot be lowered to a runtime expression",
        .return_outside_function => "'return' used outside of a function",
        .return_value_in_void_function => "return with value of type {s} in void function",
        .missing_return_value => "missing return value of type {s}",
        .return_type_mismatch => "return type mismatch: expected {s}, found {s}",
        .break_outside_loop => "'break' used outside of a loop",
        .continue_outside_loop => "'continue' used outside of a loop",
        .defer_outside_function => "'defer' only valid inside a function",
        .errdefer_outside_function => "'errdefer' only valid inside a function",
        .errdefer_in_non_error_function => "'errdefer' only valid in functions returning an error union",
        .nested_function_not_allowed => "function definitions are only allowed at top level",
        .duplicate_field => "duplicate field '{s}'",
        .duplicate_enum_field => "duplicate enum field '{s}'",
        .enum_discriminant_not_integer => "enum discriminant should be an integer literal",
        .duplicate_variant => "duplicate variant '{s}'",
        .duplicate_error_variant => "duplicate error variant '{s}'",
        .tuple_index_out_of_bounds => "tuple index {d} out of bounds (max: {d})",
        .struct_field_count_mismatch => "struct field count mismatch: expected {d}, found {d}",
        .struct_field_name_mismatch => "struct field name mismatch: expected '{s}', found '{s}'",
        .struct_field_type_mismatch => "struct field type mismatch: expected {s}, found {s}",
        .struct_missing_field => "struct literal missing required field '{s}'",
        .unknown_struct_field => "unknown field '{s}' in struct",
        .unknown_tuple_field => "unknown tuple field at index {d}",
        .unknown_module_field => "member `{s}` not found in module/file",
        .expected_pattern_on_decl_lhs => "lhs should be a pattern",
        .missing_field_name_in_struct_literal => "missing field name in struct literal",
        .unknown_enum_tag => "unknown enum tag '{s}'",
        .unknown_variant_tag => "unknown variant tag '{s}'",
        .enum_tag_type_mismatch => "enum tag '{s}' does not belong to enum {s}",
        .variant_payload_arity_mismatch => "variant payload arity mismatch: expected {d}, found {d}",
        .variant_payload_field_mismatch => "variant payload field mismatch: {s}",
        .variant_payload_field_type_mismatch => "variant payload field type mismatch: expected {s}, found {s}",
        .variant_payload_field_requires_non_null => "variant payload field '{s}' requires non-null value",
        .union_literal_multiple_fields => "union literal must specify exactly one field",
        .union_field_type_mismatch => "union field type mismatch: expected {s}, found {s}",
        .unknown_union_field => "unknown union field '{s}'",
        .union_empty_literal => "union literal must specify a field",
        .union_field_requires_non_null => "union field '{s}' requires non-null value",
        .unknown_error_tag => "unknown error tag '{s}'",
        .error_assigned_to_non_error_union => "cannot assign error {s} to non error-union type {s}",
        .invalid_use_of_orelse_on_non_optional => "'orelse' on non-optional value of type {s}",
        .orelse_type_mismatch => "'orelse' type mismatch: optional unwraps to {s}, default is {s}",
        .catch_on_non_error => "'catch' on non error-union value of type {s}",
        .catch_handler_type_mismatch => "'catch' handler type mismatch: expected {s}, found {s}",
        .invalid_optional_unwrap_target => "optional unwrap '?' on non-optional type {s}",
        .error_propagation_on_non_error => "error propagation '!' on non error-union type {s}",
        .error_propagation_mismatched_function_result => "error propagation '!' in function returning {s}, not error-union",
        .purity_violation => "purity violation: {s}",
        .struct_field_requires_non_null => "struct field '{s}' requires non-null value",
        .assign_null_to_non_optional => "cannot assign null to non-optional type {s}",
        .pointer_type_mismatch => "pointer type mismatch: expected {s}, found {s}",
        .deref_non_pointer => "cannot dereference non-pointer type {s}",
        .pointer_constness_violation => "cannot assign a *const pointer to a mutable * pointer",
        .slice_constness_violation => "cannot assign a []const slice to a mutable [] slice",
        .invalid_any_type_annotation => "invalid use of 'any' in type annotation; only allowed in parameter types",
        .wrong_arity_in_call => "wrong number of arguments: expected {d}, found {d}",
        .argument_type_mismatch => "expected argument of type {s}, found {s}",
        .call_non_callable => "attempted to call non-callable value of type {s}",
        .argument_count_mismatch => "argument count mismatch: expected {d}, found {d}",
        .null_to_non_optional_param => "null passed to non-optional parameter '{s}'",
        .undefined_identifier => "use of undefined identifier '{s}'",
        .unknown_function => "unknown function '{s}'",
        .unexpected_after_expression => "unexpected token after expression: {s}",
        .expected_comma_or_rparen => "expected ',' or ')', found {s}",
        .expected_colon_or_comma_in_param => "expected ':' (type) or ',' (next parameter), found {s}",
        .mlir_verification_failed => "MLIR verification failed: {s}",
        .mlir_block_not_a_type => "MLIR block is not a type",
        .mlir_parse_error => "failed to parse inline MLIR block: {s}",
        .mlir_splice_unknown_identifier => "unknown '@{s}' splice",
        .mlir_splice_not_comptime => "'@{s}' must name a comptime value or type",
        .mlir_splice_unbound => "no comptime binding available for '@{s}'",
        .mlir_operation_missing_result_type => "inline MLIR operation must have an explicit result type",
        .comptime_type_not_supported => "comptime type not supported",
        .package_missing_declaration => "missing package declaration; expected 'package {s}'",
        .entry_package_missing => "entry modules must declare 'package main'",
        .entry_package_not_main => "entry modules must declare 'package main'; found '{s}'",
        .checker_internal_error => "internal checker error: {s}",
        .tir_lowering_failed => "TIR lowering failed in this file",
        .tir_variant_tag_not_found => "TIR: unknown variant tag: {s}",
        .tir_codegen_missing_operand => "codegen: missing operand for {s}",
        .import_cycle_detected => "import cycle detected: {s}",
        .imports_blocked_by_cycle => "imports blocked by cycle: {s}",
        .unused_function => "unused function '{s}' is never referenced",
        .unused_param => "unused parameter '{s}'",
        .unused_variable => "unused local variable '{s}'",
    };
}

pub const NoteCode = enum {
    unexpected_token_here,
    expected_identifier_or_keyword,
    did_you_mean_equal,
    token_cannot_start_expression,
    operator_cannot_be_used_here,
    expected_field_name_or_index_note,
    separate_parameters,
    labeled_loops,
    use_literal_constant_or_binding,
    use_literal_constant_or_simple_binding,
    use_single_identifier,
    provide_element_type_last,
    attribute_names_identifiers_or_keywords,
    expected_map_type_or_literal_continuation_note,
    expected_array_type_or_literal_continuation,
    attribute_values_literals_or_identifiers,
    use_extern_async_proc_or_fn,
    use_extern_proc_fn_or_type,
    use_colon_for_type_or_comma_or_paren,
    token_cannot_start_pattern,
    expected_token_note,
    found_token_note,
    try_inserting_token,
    this_token_starts_new_stmt,
    pattern_binding_help,
    exhaustiveness_hint,
    did_you_mean,
    did_you_mean_field,
    did_you_mean_tag,
    available_fields,
    available_tags,
    add_wildcard,
    missing_fields_list,
    function_signature,
    try_cast,
    remove_annotation,
    first_defined_here,
    expected_return_type,
    constness_explanation,
    try_const,
    search_paths,
    receiver_explanation,
    try_address_of,
    make_optional,
    wrong_operator,
    value_already_present,
    array_elements_count,
    first_type_mismatch,
    add_type_annotation,
    add_else_branch,
    try_else,
    requires_loop_context,
    requires_function_context,
    requires_async_context,
    make_async,
    defer_context_requirement,
    use_defer,
    top_level_only,
    use_closure,
    tuple_size,
    cast_alternatives,
    check_divisor,
    previous_arm_covers,
    prefix_underscore,
    purity_explanation,
    remove_pure,
    cycle_path,
    break_cycle,
    mlir_help,
    comptime_limitation,
};

pub fn diagnosticNoteFmt(code: NoteCode) []const u8 {
    return switch (code) {
        .unexpected_token_here => "unexpected token here",
        .expected_identifier_or_keyword => "use an identifier like 'foo' or a keyword like 'struct'",
        .did_you_mean_equal => "did you mean '=' before the initializer?",
        .token_cannot_start_expression => "this token cannot start or continue an expression here",
        .operator_cannot_be_used_here => "this operator cannot be used here",
        .expected_field_name_or_index_note => "use a field name like .foo or a tuple index like .0",
        .separate_parameters => "separate parameters with ',' and end the list with '|'",
        .labeled_loops => "labeled loops: label: for ... { ... } or label: while ... { ... }",
        .use_literal_constant_or_binding => "use a literal, constant path, or a binding name",
        .use_literal_constant_or_simple_binding => "use a literal, constant path, or a simple binding",
        .use_single_identifier => "use a single identifier without dots",
        .provide_element_type_last => "provide the element type as the last argument, and shape dimensions before it",
        .attribute_names_identifiers_or_keywords => "attribute names can be identifiers or keywords",
        .expected_map_type_or_literal_continuation_note => "use ']' to end a map type or ',' to separate key-value pairs in a map literal",
        .expected_array_type_or_literal_continuation => "use ']' to end an array type or literal, ':' for a map type/literal, or ',' to separate elements in an array literal",
        .attribute_values_literals_or_identifiers => "attribute values must be literals or identifiers",
        .use_extern_async_proc_or_fn => "use 'extern async proc' or 'extern async fn'",
        .use_extern_proc_fn_or_type => "use 'extern proc', 'extern fn', or 'extern struct/enum/union'",
        .use_colon_for_type_or_comma_or_paren => "use ':' to specify a type, or ',' / ')' to end the parameter",
        .token_cannot_start_pattern => "this token cannot start a pattern here",
        .expected_token_note => "expected token: {s}",
        .found_token_note => "found token: {s}",
        .try_inserting_token => "try inserting: {s}",
        .this_token_starts_new_stmt => "this token starts a new statement: {s}",
        .pattern_binding_help => "all arms of an 'or' pattern must bind the same variables with the same types",
        .exhaustiveness_hint => "missing cases: {s}",
        .did_you_mean => "did you mean '{s}'?",
        .did_you_mean_field => "did you mean '{s}'?",
        .did_you_mean_tag => "did you mean '{s}'?",
        .available_fields => "available fields: {s}",
        .available_tags => "available tags: {s}",
        .add_wildcard => "consider adding a wildcard pattern: {s}",
        .missing_fields_list => "missing required fields: {s}",
        .function_signature => "function signature: {s}",
        .try_cast => "try casting explicitly: {s}",
        .remove_annotation => "try removing the type annotation",
        .first_defined_here => "first defined here",
        .expected_return_type => "function signature: {s}",
        .constness_explanation => "const pointers cannot be assigned to mutable pointers (would violate const guarantees)",
        .try_const => "try declaring as: {s}",
        .search_paths => "searched in: {s}",
        .receiver_explanation => "method signature: {s}",
        .try_address_of => "try: {s}",
        .make_optional => "try making the type optional: {s}",
        .wrong_operator => "'{s}' is for optional or error types",
        .value_already_present => "value is already present, no need for 'orelse'",
        .array_elements_count => "array literal has {d} elements",
        .first_type_mismatch => "first element has type {s} (at index 0)",
        .add_type_annotation => "try: {s}",
        .add_else_branch => "when 'if' is used as an expression, both branches must produce a value",
        .try_else => "try: {s}",
        .requires_loop_context => "'break' and 'continue' can only be used inside 'for' or 'while' loops",
        .requires_function_context => "'return' can only be used inside function bodies",
        .requires_async_context => "'await' can only be used in async functions",
        .make_async => "try making the function async: {s}",
        .defer_context_requirement => "'defer'/'errdefer' have specific context requirements",
        .use_defer => "use 'defer' instead for non-error functions",
        .top_level_only => "functions must be defined at module scope, not inside other functions",
        .use_closure => "consider using a closure instead: {s}",
        .tuple_size => "tuple has {d} elements (indices 0-{d})",
        .cast_alternatives => "consider using: {s}",
        .check_divisor => "if divisor is a runtime value, add a check: if divisor != 0 { ... }",
        .previous_arm_covers => "this case is already covered by a previous arm",
        .prefix_underscore => "prefix with an underscore to indicate it's intentionally unused: `_{s}`",
        .purity_explanation => "purity violation: {s}",
        .remove_pure => "remove 'pure' annotation or make function non-pure",
        .cycle_path => "cycle: {s}",
        .break_cycle => "consider extracting shared code into a separate module",
        .mlir_help => "see MLIR documentation: {s}",
        .comptime_limitation => "this comptime feature is not yet implemented",
    };
}

pub const Note = struct {
    loc: ?Loc = null,
    code: NoteCode,
    payload: MessagePayload = .none,
    next_note: u32,
};

pub const Message = struct {
    severity: Severity,
    loc: Loc,
    code: DiagnosticCode,
    payload: MessagePayload,
    first_note: u32,
};

pub const Diagnostics = struct {
    allocator: std.mem.Allocator,
    messages: std.ArrayListUnmanaged(Message) = .{},
    notes: std.ArrayListUnmanaged(Note) = .{},
    mutex: std.Thread.Mutex = .{},
    type_store: ?*types.TypeStore = null,
    str_interner: ?*types.StringInterner = null,

    const NO_NOTE: u32 = 0xFFFFFFFF;

    pub const NoteIter = struct {
        diags: *Diagnostics,
        idx: u32,

        pub fn next(self: *NoteIter) ?Note {
            if (self.idx == NO_NOTE) return null;
            const note = self.diags.notes.items[self.idx];
            self.idx = note.next_note;
            return note;
        }
    };

    pub fn init(allocator: std.mem.Allocator, type_store: ?*types.TypeStore, str_interner: ?*types.StringInterner) Diagnostics {
        return .{ .allocator = allocator, .type_store = type_store, .str_interner = str_interner };
    }

    pub fn deinit(self: *Diagnostics) void {
        self.messages.deinit(self.allocator);
        self.notes.deinit(self.allocator);
    }

    pub fn addError(self: *Diagnostics, loc: Loc, comptime code: DiagnosticCode, args: anytype) !void {
        try self.addMessage(.err, loc, code, args);
    }
    pub fn addWarning(self: *Diagnostics, loc: Loc, comptime code: DiagnosticCode, args: anytype) !void {
        try self.addMessage(.warning, loc, code, args);
    }
    pub fn addNote(self: *Diagnostics, loc: Loc, comptime code: DiagnosticCode, args: anytype) !void {
        try self.addMessage(.note, loc, code, args);
    }

    fn payloadFromArgs(args: anytype) MessagePayload {
        const info = @typeInfo(@TypeOf(args)).@"struct";
        const n = info.fields.len;
        if (n == 0) return .none;
        if (n == 1) {
            const f0 = info.fields[0];
            const v0 = @field(args, f0.name);
            if (f0.type == []const u8) return .{ .string = v0 };
            if (f0.type == ast.StrId) return .{ .str_id = v0 };
            if (f0.type == types.TypeId) return .{ .type_id = v0 };
            if (@typeInfo(f0.type) == .int) return .{ .integer = @intCast(v0) };
            return .{ .one = .{ .a = convertToPayloadTag(v0) } };
        } else if (n == 2) {
            const f0 = info.fields[0];
            const f1 = info.fields[1];
            const v0 = @field(args, f0.name);
            const v1 = @field(args, f1.name);
            if (f0.type == types.TypeId and f1.type == types.TypeId) return .{ .two_type_ids = .{ .a = v0, .b = v1 } };
            if (@typeInfo(f0.type) == .int or @typeInfo(f1.type) == .int) return .{ .two_integers = .{ .a = @intCast(v0), .b = @intCast(v1) } };
            if (f0.type == ast.StrId and f1.type == types.TypeId) return .{ .string_and_type = .{ .s = v0, .t = v1 } };
            return .{ .two = .{ .a = convertToPayloadTag(v0), .b = convertToPayloadTag(v1) } };
        } else if (n == 3) {
            const f0 = info.fields[0];
            const f1 = info.fields[1];
            const f2 = info.fields[2];
            const v0 = @field(args, f0.name);
            const v1 = @field(args, f1.name);
            const v2 = @field(args, f2.name);
            if (f0.type == ast.StrId and f1.type == ast.StrId and f2.type == types.TypeId) return .{ .two_strings_and_type = .{ .s1 = v0, .s2 = v1, .t = v2 } };
            return .{ .three = .{ .a = convertToPayloadTag(v0), .b = convertToPayloadTag(v1), .c = convertToPayloadTag(v2) } };
        }
        @compileError("Max 3 args");
    }

    fn addMessage(self: *Diagnostics, sev: Severity, loc: Loc, comptime code: DiagnosticCode, args: anytype) !void {
        self.mutex.lock();
        defer self.mutex.unlock();
        const payload = if (@typeInfo(@TypeOf(args)).@"struct".fields.len == 0) .none else payloadFromArgs(args);
        // dedup
        for (self.messages.items) |m| {
            if (m.severity == sev and m.code == code and std.meta.eql(m.loc, loc) and std.meta.eql(m.payload, payload)) return;
        }
        self.messages.append(self.allocator, .{ .severity = sev, .loc = loc, .code = code, .payload = payload, .first_note = NO_NOTE }) catch oom();
    }

    pub fn attachNote(self: *Diagnostics, idx: usize, loc: ?Loc, comptime code: NoteCode) !void {
        try self.attachNoteArgs(idx, loc, code, .{});
    }

    pub fn attachNoteArgs(self: *Diagnostics, idx: usize, loc: ?Loc, comptime code: NoteCode, args: anytype) !void {
        self.mutex.lock();
        defer self.mutex.unlock();
        if (idx >= self.messages.items.len) return;
        const payload = payloadFromArgs(args);
        const note_idx: u32 = @intCast(self.notes.items.len);
        self.notes.append(self.allocator, .{ .loc = loc, .code = code, .payload = payload, .next_note = NO_NOTE }) catch oom();

        // Append note to the end of the linked list for this message
        var curr = &self.messages.items[idx].first_note;
        while (curr.* != NO_NOTE) {
            curr = &self.notes.items[curr.*].next_note;
        }
        curr.* = note_idx;
    }

    pub fn anyErrors(self: *Diagnostics) bool {
        for (self.messages.items) |m| if (m.severity == .err) return true;
        return false;
    }
    pub fn anyWarnings(self: *Diagnostics) bool {
        for (self.messages.items) |m| if (m.severity == .warning) return true;
        return false;
    }
    pub fn count(self: *Diagnostics) usize {
        return self.messages.items.len;
    }

    pub fn joinStrings(allocator: std.mem.Allocator, sep: []const u8, items: []const []const u8) ![]const u8 {
        if (items.len == 0) return try allocator.alloc(u8, 0);
        var len: usize = sep.len * (items.len - 1);
        for (items) |item| len += item.len;
        const buf = try allocator.alloc(u8, len);
        var off: usize = 0;
        for (items, 0..) |item, i| {
            if (i > 0) {
                @memcpy(buf[off..][0..sep.len], sep);
                off += sep.len;
            }
            @memcpy(buf[off..][0..item.len], item);
            off += item.len;
        }
        return buf;
    }

    pub fn noteIterator(self: *Diagnostics, message: Message) NoteIter {
        return .{ .diags = self, .idx = message.first_note };
    }

    pub fn messageToOwnedSlice(self: *Diagnostics, allocator: std.mem.Allocator, message: Message) ![]u8 {
        var buf = std.ArrayList(u8){};
        defer buf.deinit(allocator);
        if (self.type_store == null or self.str_interner == null) {
            try buf.writer(allocator).writeAll("Internal Error: Diagnostic context missing");
            return buf.toOwnedSlice(allocator);
        }
        try writeInterpolated(buf.writer(allocator), diagnosticMessageFmt(message.code), message.payload, .{ .type_store = self.type_store.?, .str_interner = self.str_interner.?, .gpa = allocator });
        return buf.toOwnedSlice(allocator);
    }

    pub fn noteToOwnedSlice(self: *Diagnostics, allocator: std.mem.Allocator, note: Note) ![]u8 {
        var buf = std.ArrayList(u8){};
        defer buf.deinit(allocator);
        if (self.type_store == null or self.str_interner == null) {
            try buf.writer(allocator).writeAll("Internal Error: Diagnostic context missing");
            return buf.toOwnedSlice(allocator);
        }
        try writeInterpolated(buf.writer(allocator), diagnosticNoteFmt(note.code), note.payload, .{ .type_store = self.type_store.?, .str_interner = self.str_interner.?, .gpa = allocator });
        return buf.toOwnedSlice(allocator);
    }

    pub fn emit(self: *Diagnostics, context: *Context, writer: anytype) !void {
        try self.emitStyled(context, writer, true);
    }

    pub fn emitStyled(self: *Diagnostics, context: *Context, writer: anytype, color: bool) !void {
        const ctx = DiagnosticContext{ .type_store = context.type_store, .str_interner = context.interner, .gpa = context.gpa };
        var source_map = std.AutoArrayHashMap(usize, []const u8).init(context.gpa);
        defer source_map.deinit();

        for (self.messages.items) |m| {
            if (m.severity != .err) continue; // Simplification: print errors primarily, can change logic if needed
            const src = source_map.get(m.loc.file_id) orelse blk: {
                const d = try context.source_manager.read(m.loc.file_id);
                try source_map.put(m.loc.file_id, d);
                break :blk d;
            };
            const lc = lineCol(src, m.loc.start);
            if (color) try writer.print("\x1b[36m", .{});
            try writer.print("{s}:{d}:{d}: ", .{ context.source_manager.get(m.loc.file_id) orelse "unknown", lc.line + 1, lc.col + 1 });
            if (color) try writer.print("\x1b[0m", .{});

            const sev_col = switch (m.severity) {
                .err => "\x1b[31m",
                .warning => "\x1b[33m",
                .note => "\x1b[34m",
            };
            const sev_str = switch (m.severity) {
                .err => "error",
                .warning => "warning",
                .note => "note",
            };
            if (color) try writer.print("\x1b[1m{s}{s}\x1b[0m\x1b[1m: ", .{ sev_col, sev_str });
            try writeInterpolated(writer, diagnosticMessageFmt(m.code), m.payload, ctx);
            if (color) {
                try writer.print("\x1b[0m\n", .{});
            } else try writer.writeByte('\n');

            const line_slice = src[lc.line_start..lc.line_end];
            const line_no = lc.line + 1;
            const width = digits(line_no);
            const pad = if (width > 16) 16 else width;
            var num_pad: [16]u8 = .{' '} ** 16;
            const p = if (width > digits(line_no)) width - digits(line_no) else 0;

            try writer.print("{s}{d} \x1b[36m▌\x1b[0m {s}\n", .{ num_pad[0..p], line_no, line_slice });
            try writer.print(" {s}\x1b[36m▌\x1b[0m ", .{num_pad[0..pad]});

            var i: usize = 0;
            while (i < lc.col) : (i += 1) try writer.writeByte(' ');
            if (color) try writer.print("{s}", .{sev_col});
            const span = if (m.loc.end > m.loc.start and m.loc.end <= lc.line_end) (m.loc.end - m.loc.start) else 1;
            i = 0;
            while (i < span) : (i += 1) try writer.writeByte('^');
            if (color) {
                try writer.print("\x1b[0m\n", .{});
            } else try writer.writeByte('\n');

            var nid = m.first_note;
            while (nid != NO_NOTE) {
                const n = self.notes.items[nid];
                try writer.print(" {s}= \x1b[34mnote[{s}]\x1b[0m: ", .{ num_pad[0..pad], @tagName(n.code) });
                try writeInterpolated(writer, diagnosticNoteFmt(n.code), n.payload, ctx);
                if (n.loc) |nl| {
                    const nlc = lineCol(src, nl.start);
                    try writer.print(" (at \x1b[36m{d}:{d}\x1b[0m)", .{ nlc.line + 1, nlc.col + 1 });
                }
                try writer.writeByte('\n');
                nid = n.next_note;
            }
            try writer.writeByte('\n');
        }
        try writer.flush();
    }

    fn writeInterpolated(writer: anytype, fmt: []const u8, payload: MessagePayload, context: DiagnosticContext) !void {
        var start: usize = 0;
        var i: usize = 0;
        var args_idx: usize = 0;
        while (i < fmt.len) {
            if (i + 2 < fmt.len and fmt[i] == '{' and fmt[i + 2] == '}') {
                if (i > start) try writer.print("{s}", .{fmt[start..i]});
                try printPayloadArg(writer, payload, args_idx, context, fmt[i + 1]);
                args_idx += 1;
                i += 3;
                start = i;
            } else {
                i += 1;
            }
        }
        if (start < fmt.len) try writer.print("{s}", .{fmt[start..]});
    }

    fn printPayloadArg(writer: anytype, payload: MessagePayload, index: usize, context: DiagnosticContext, spec: u8) !void {
        switch (payload) {
            .none => {},
            .string => |s| if (index == 0 and spec == 's') try writer.writeAll(s),
            .str_id => |id| if (index == 0 and spec == 's') try writer.writeAll(context.str_interner.get(id)),
            .type_id => |id| if (index == 0 and spec == 's') try context.type_store.formatTypeForDiagnostic(id, .{}, writer),
            .two_type_ids => |ids| if (spec == 's') {
                if (index == 0) try context.type_store.formatTypeForDiagnostic(ids.a, .{}, writer) else if (index == 1) try context.type_store.formatTypeForDiagnostic(ids.b, .{}, writer);
            },
            .one => |p| if (index == 0 and spec == 's') try printTag(writer, p.a),
            .two => |p| if (spec == 's') {
                if (index == 0) try printTag(writer, p.a) else if (index == 1) try printTag(writer, p.b);
            },
            .three => |p| if (spec == 's') {
                if (index == 0) try printTag(writer, p.a) else if (index == 1) try printTag(writer, p.b) else if (index == 2) try printTag(writer, p.c);
            },
            .integer => |val| if (spec == 'd' and index == 0) try writer.print("{d}", .{val}),
            .two_integers => |vals| if (spec == 'd') {
                if (index == 0) try writer.print("{d}", .{vals.a}) else if (index == 1) try writer.print("{d}", .{vals.b});
            },
            .string_and_type => |sat| if (spec == 's') {
                if (index == 0) try writer.writeAll(context.str_interner.get(sat.s)) else if (index == 1) try context.type_store.formatTypeForDiagnostic(sat.t, .{}, writer);
            },
            .two_strings_and_type => |tst| if (spec == 's') {
                if (index == 0) try writer.writeAll(context.str_interner.get(tst.s1)) else if (index == 1) try writer.writeAll(context.str_interner.get(tst.s2)) else if (index == 2) try context.type_store.formatTypeForDiagnostic(tst.t, .{}, writer);
            },
        }
    }

    fn printTag(writer: anytype, tag: PayloadTag) !void {
        var buf: [64]u8 = undefined;
        try writer.writeAll(std.ascii.lowerString(&buf, @tagName(tag)));
    }

    const LineCol = struct { line: usize, col: usize, line_start: usize, line_end: usize };
    fn lineCol(src: []const u8, idx: usize) LineCol {
        var i: usize = 0;
        var line: usize = 0;
        var last_nl: usize = 0;
        while (i < src.len and i < idx) : (i += 1) {
            if (src[i] == '\n') {
                line += 1;
                last_nl = i + 1;
            }
        }
        var end: usize = idx;
        while (end < src.len and src[end] != '\n' and src[end] != '\r') : (end += 1) {}
        return .{ .line = line, .col = idx - last_nl, .line_start = last_nl, .line_end = end };
    }
    fn digits(n: usize) usize {
        var v = n;
        var c: usize = 1;
        while (v >= 10) : (v /= 10) c += 1;
        return c;
    }
};

pub fn joinStrings(allocator: std.mem.Allocator, sep: []const u8, items: []const []const u8) ![]const u8 {
    return Diagnostics.joinStrings(allocator, sep, items);
}
