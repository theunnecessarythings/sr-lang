const std = @import("std");
const Loc = @import("lexer.zig").Token.Loc;
const Tag = @import("lexer.zig").Token.Tag;
const Context = @import("compile.zig").Context;
const BinaryOp = @import("ast.zig").BinaryOp;
const UnaryOp = @import("ast.zig").UnaryOp;
const types = @import("types.zig");
const TypeKind = types.TypeKind;

pub const Severity = enum {
    err,
    warning,
    note,
};

fn payloadTag() type {
    // combine Tag enum BinOp enum and UnOp enum into one
    const tag_fields = std.meta.fields(Tag);
    const binop_fields = std.meta.fields(BinaryOp);
    const unop_fields = std.meta.fields(UnaryOp);
    const type_kind_fields = std.meta.fields(TypeKind);
    const fields = tag_fields ++ binop_fields ++ unop_fields ++ type_kind_fields;

    var enum_fields: [fields.len]std.builtin.Type.EnumField = undefined;
    var decls = [_]std.builtin.Type.Declaration{};
    inline for (fields, 0..) |field, i| {
        enum_fields[i] = .{
            .name = field.name,
            .value = i,
        };
    }
    return @Type(.{
        .@"enum" = .{
            .tag_type = std.math.IntFittingRange(0, fields.len - 1),
            .fields = &enum_fields,
            .decls = &decls,
            .is_exhaustive = true,
        },
    });
}

const PayloadTag = payloadTag();

fn convertToPayloadTag(value: anytype) PayloadTag {
    const tag_field_count = std.meta.fields(Tag).len;
    const binop_field_count = std.meta.fields(BinaryOp).len;
    const unop_field_count = std.meta.fields(UnaryOp).len;
    const int_value = @intFromEnum(value);
    switch (@TypeOf(value)) {
        Tag => return @enumFromInt(int_value),
        BinaryOp => return @enumFromInt(int_value + tag_field_count),
        UnaryOp => return @enumFromInt(int_value + tag_field_count + binop_field_count),
        TypeKind => return @enumFromInt(int_value + tag_field_count + binop_field_count + unop_field_count),
        else => @compileError("Unsupported type for PayloadTag"),
    }
}

const MessagePayload = union(enum) {
    none,
    string: []const u8,
    one: struct { a: PayloadTag },
    two: struct { a: PayloadTag, b: PayloadTag },
    three: struct { a: PayloadTag, b: PayloadTag, c: PayloadTag },
};

pub const DiagnosticCode = enum {
    // Lexer / parser level
    unexpected_token, // payload: one (found)
    unexpected_closing_delimiter, // payload: one (found)
    mismatched_closing_delimiter, // payload: two (expected, found)
    expected_identifier, // payload: one (found)
    expected_expression_after_operator, // payload: one (operator)
    expected_type_in_declaration, // payload: one (found)
    expected_field_name_or_index, // payload: one (found)
    expected_closure_param_separator, // payload: one (found)
    expected_loop_after_label, // payload: one (found)
    unexpected_postfix_operator, // payload: one (operator)
    unexpected_token_in_expression, // payload: one (found)
    invalid_float_literal, // payload: one (offending token)
    invalid_integer_literal, // payload: one (offending token)
    invalid_imaginary_literal, // payload: one (offending token)
    expected_attribute_name, // payload: one (found)
    expected_map_type_or_literal_continuation, // payload: one (found)
    expected_array_like_continuation, // payload: one (found)
    expected_attribute_value, // payload: one (found)
    expected_extern_async_function, // payload: one (found)
    expected_extern_declaration, // payload: one (found)
    expected_parameter_type_or_end, // payload: one (found)
    invalid_import_operand, // payload: one (found)
    import_not_found, // payload: one (path)
    invalid_package_name,

    // Pattern / matching
    token_cannot_start_pattern, // payload: one (found)
    unexpected_token_in_pattern, // payload: one (found)
    invalid_binding_name_in_at_pattern, // payload: one (found)
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

    // Type/form checking
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
    cannot_infer_range_type,
    could_not_resolve_type, // payload: one (offending token)
    map_wrong_key_type,
    map_mixed_key_types,
    map_mixed_value_types,
    noreturn_not_storable,
    type_value_mismatch,
    type_annotation_mismatch,
    mlir_block_not_a_type,

    // Casts / conversions
    cast_target_not_type,
    invalid_cast, // broad catch-all (left for back-compat)
    invalid_checked_cast,
    invalid_bitcast,
    bitcast_non_numeric_or_pointer,
    bitcast_target_non_numeric_or_pointer,
    numeric_cast_on_non_numeric,
    bitcast_size_unknown,

    // Operators / expressions
    invalid_binary_op_operands, // payload: three (op, lhs token, rhs token)
    invalid_unary_op_operand, // payload: two (op, operand token)
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

    // Async/await
    await_non_async,
    await_type_mismatch,
    await_outside_async_context,

    // Values / indexing / fields
    field_access_on_non_aggregate,
    invalid_struct_field_index, // payload: one (found)
    not_indexable,
    non_integer_index, // payload: one (found)
    invalid_index_type, // payload: one (found)

    // Types
    expected_array_type, // payload: one (found)
    expected_tensor_type,
    expected_map_type, // payload: one (found)
    expected_struct_type, // payload: one (found)
    expected_enum_type, // payload: one (found)
    expected_tuple_type, // payload: one (found)
    expected_pointer_type, // payload: one (found)
    expected_integer_type, // payload: one (found)
    expected_float_type, // payload: one (found)

    // Methods
    method_requires_function_value,
    method_requires_self_parameter,
    method_self_must_be_binding,
    method_self_requires_type,
    method_self_type_mismatch,
    method_owner_not_struct,
    method_invalid_owner_path,
    duplicate_method_on_type, // payload: one (method name)
    method_receiver_requires_pointer,
    method_receiver_requires_value,
    method_receiver_not_addressable,

    // Decls / control flow
    checker_insert_not_expanded,
    checker_comptime_not_executed,
    checker_code_block_not_executed,
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

    // Structs/tuples/enums/unions
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

    // Variants
    unknown_enum_tag,
    unknown_variant_tag,
    enum_tag_type_mismatch,
    variant_payload_arity_mismatch,
    variant_payload_field_mismatch,
    variant_payload_field_type_mismatch,
    variant_payload_field_requires_non_null,

    // Unions
    union_literal_multiple_fields,
    union_field_type_mismatch,
    unknown_union_field,
    union_empty_literal,
    union_field_requires_non_null,

    // Errors / optionals / purity
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

    // Pointers
    pointer_type_mismatch,
    deref_non_pointer,
    pointer_constness_violation,

    // Calls
    wrong_arity_in_call,
    argument_type_mismatch,
    call_non_callable,
    argument_count_mismatch,
    null_to_non_optional_param,

    // Names
    undefined_identifier,
    unknown_function,

    // New, more specific variants for common vague errors (opt-in)
    unexpected_after_expression, // payload: one (found)
    expected_comma_or_rparen, // payload: one (found)
    expected_colon_or_comma_in_param, // payload: one (found)

    mlir_verification_failed,
    mlir_parse_error,
    mlir_splice_unknown_identifier,
    mlir_splice_not_comptime,
    mlir_splice_unbound,

    comptime_type_not_supported,
    package_missing_declaration,
    entry_package_missing,
    entry_package_not_main,
    checker_internal_error,
    // TIR lowering (temporary diagnostics for debugging)
    tir_lowering_failed,
    tir_variant_tag_not_found,
    tir_codegen_missing_operand,
    // Module/import cycles
    import_cycle_detected,
    imports_blocked_by_cycle,
    unused_function,
    unused_param,
    unused_variable,
};

pub fn diagnosticMessageFmt(code: DiagnosticCode) []const u8 {
    return switch (code) {
        // Lexer / parser level
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
        .invalid_float_literal => "invalid float literal",
        .invalid_integer_literal => "invalid integer literal",
        .invalid_imaginary_literal => "invalid imaginary literal",
        .expected_attribute_name => "expected attribute name, found {s}",
        .expected_map_type_or_literal_continuation => "expected ']' or ',' in map type/literal, found {s}",
        .expected_array_like_continuation => "expected ']', ':', or ',' in array-like, found {s}",
        .expected_attribute_value => "expected literal or identifier after '=', found {s}",
        .expected_extern_async_function => "expected 'proc' or 'fn' after 'extern async', found {s}",
        .expected_extern_declaration => "expected 'proc', 'fn', or a type after 'extern', found {s}",
        .expected_parameter_type_or_end => "expected ':', ',', or ')' after parameter, found {s}",
        .invalid_import_operand => "invalid import operand; expected string-like path, found {s}",
        .import_not_found => "the path specified in import was not found",
        .invalid_package_name => "invalid package name",

        // Pattern / matching
        .token_cannot_start_pattern => "this token cannot start a pattern: {s}",
        .unexpected_token_in_pattern => "unexpected token in pattern: {s}",
        .invalid_binding_name_in_at_pattern => "only simple identifier paths can be used as binding names in '@' patterns; found {s}",
        .underscore_not_const_in_range_pattern => "'_' is not valid as a constant in a range pattern",
        .left_side_not_const_like_in_range_pattern => "left side of a range pattern must be const-like",
        .descending_range_pattern => "descending or empty range pattern",
        .string_equality_in_match_not_supported => "string equality in 'match' is not supported",
        .pattern_shape_mismatch => "pattern does not match the shape of the value",
        .pattern_type_mismatch => "pattern type does not match value type",
        .or_pattern_binding_mismatch => "bindings in 'or' pattern arms do not match",
        .or_pattern_binding_type_mismatch => "bindings in 'or' pattern arms have mismatched types",
        .empty_path_pattern => "empty path pattern",
        .unknown_type_in_path => "unknown type in path pattern",
        .unsupported_pattern_type => "unsupported pattern type",

        // Type/form checking
        .tensor_missing_arguments => "expected at least one argument to 'tensor', found none",
        .tensor_missing_element_type => "tensor is missing the element type",
        .tensor_dimension_not_integer_literal => "tensor dimensions must be integer literals",
        .tensor_rank_exceeds_limit => "tensor rank exceeds supported maximum of {d}",
        .tensor_rank_mismatch => "tensor rank mismatch",
        .tensor_dimension_mismatch => "tensor dimensions do not match",
        .tensor_element_type_mismatch => "tensor element type mismatch",
        .simd_lanes_not_integer_literal => "SIMD lanes must be an integer literal",
        .simd_invalid_element_type => "invalid SIMD element type",
        .array_size_not_integer_literal => "array size must be an integer literal",
        .array_length_mismatch => "array literal length does not match declared size",
        .heterogeneous_array_elements => "array elements must have a uniform type",
        .cannot_infer_type_from_empty_array => "cannot infer type from empty array literal; add a type annotation",
        .cannot_infer_range_type => "cannot infer type from range with no start or end value; add a type annotation to at least one side",
        .could_not_resolve_type => "could not resolve type: {s}",
        .map_wrong_key_type => "map index has wrong key type",
        .map_mixed_key_types => "map literal has mixed key types",
        .map_mixed_value_types => "map literal has mixed value types",
        .noreturn_not_storable => "type 'noreturn' cannot be used as a variable or struct field type",
        .type_value_mismatch => "type/value mismatch; expected a type",
        .type_annotation_mismatch => "type annotation does not match initializer",

        // Casts / conversions
        .cast_target_not_type => "cast target is not a type",
        .invalid_cast => "invalid cast between incompatible types {s} and {s}",
        .invalid_checked_cast => "checked cast cannot succeed",
        .invalid_bitcast => "invalid bitcast between incompatible types {s} and {s}",
        .bitcast_non_numeric_or_pointer => "bitcast source must be numeric or a pointer type",
        .bitcast_target_non_numeric_or_pointer => "bitcast target must be numeric or a pointer type",
        .numeric_cast_on_non_numeric => "numeric cast applied to non-numeric type",
        .bitcast_size_unknown => "cannot determine size for bitcast",

        // Operators / expressions
        .invalid_binary_op_operands => "invalid operands for binary operator '{s}': '{s}' and '{s}'",
        .invalid_unary_op_operand => "invalid operand for unary operator '{s}': '{s}'",
        .division_by_zero => "division by zero",
        .in_operator_not_supported => "'in' operator is not implemented yet",
        .non_boolean_condition => "condition expression expected boolean type, got '{s}'",
        .if_expression_requires_else => "'if' used as an expression must have an 'else' branch",
        .if_branch_type_mismatch => "if branches produce mismatched types",
        .range_type_mismatch => "range expression has mismatched types",
        .range_requires_integer_operands => "range expressions only work with integer operands",
        .while_expression_not_value => "'while' cannot be used as a value (no resulting expression)",
        .non_iterable_in_for => "value is not iterable in 'for' loop",
        .tuple_arity_mismatch => "tuple pattern arity does not match value",
        .struct_pattern_field_mismatch => "struct pattern fields do not match value",
        .variant_payload_mismatch => "variant pattern payload does not match",
        .non_exhaustive_match => "non-exhaustive match; missing cases",
        .overlapping_match_arm => "overlapping or duplicate match arm",
        .unreachable_match_arm => "unreachable match arm (covered by previous arms)",
        .loop_break_value_type_conflict => "loop break values have conflicting types",
        .assignment_type_mismatch => "assigned value does not match the variable's type",
        .unreachable_code_after_break => "unreachable code after an unconditional break",

        // Async/await
        .await_non_async => "'await' applied to a non-async expression",
        .await_type_mismatch => "awaited expression type does not match expected type",
        .await_outside_async_context => "'await' used outside of an async context",

        // Values / indexing / fields
        .field_access_on_non_aggregate => "field access on non-aggregate value, {s}",
        .invalid_struct_field_index => "numeric field access is invalid on a struct; found {s}",
        .not_indexable => "value is not indexable",
        .non_integer_index => "array index must be an integer; found {s}",
        .invalid_index_type => "invalid index type; found {s}",

        // Types
        .expected_array_type => "expected array type, found {s}",
        .expected_tensor_type => "expected tensor type",
        .expected_map_type => "expected map type, found {s}",
        .expected_struct_type => "expected struct type, found {s}",
        .expected_enum_type => "expected enum type, found {s}",
        .expected_tuple_type => "expected tuple type, found {s}",
        .expected_pointer_type => "expected pointer type, found {s}",
        .expected_integer_type => "expected integer type, found {s}",
        .expected_float_type => "expected float type, found {s}",

        // Methods
        .method_requires_function_value => "methods must be defined with a function value",
        .method_requires_self_parameter => "methods must declare a 'self' parameter as the first argument",
        .method_self_must_be_binding => "the first parameter of a method must bind to 'self'",
        .method_self_requires_type => "the 'self' parameter of a method requires an explicit type",
        .method_self_type_mismatch => "method 'self' parameter must match the enclosing struct type",
        .method_owner_not_struct => "methods can only be declared on struct, union, enum, variant, or error types",
        .method_invalid_owner_path => "methods must be declared on a simple struct name",
        .duplicate_method_on_type => "duplicate method '{s}' for this struct",
        .method_receiver_requires_pointer => "method '{s}' requires a pointer receiver",
        .method_receiver_requires_value => "method '{s}' requires a value receiver",
        .method_receiver_not_addressable => "method '{s}' requires an addressable receiver",

        // Decls / control flow
        .checker_insert_not_expanded => "checker: insert not expanded yet; walking only",
        .checker_comptime_not_executed => "checker: comptime not executed; walking only",
        .checker_code_block_not_executed => "checker: code block not executed; walking only",
        .return_outside_function => "'return' used outside of a function",
        .return_value_in_void_function => "return with a value in a void function",
        .missing_return_value => "missing return value",
        .return_type_mismatch => "return type does not match function signature",
        .break_outside_loop => "'break' used outside of a loop",
        .continue_outside_loop => "'continue' used outside of a loop",
        .defer_outside_function => "'defer' only valid inside a function",
        .errdefer_outside_function => "'errdefer' only valid inside a function",
        .errdefer_in_non_error_function => "'errdefer' only valid in functions returning an error union",
        .nested_function_not_allowed => "function definitions are only allowed at top level",

        // Structs/tuples/enums/unions
        .duplicate_field => "duplicate field",
        .duplicate_enum_field => "duplicate enum field",
        .enum_discriminant_not_integer => "enum discriminant should be an integer literal",
        .duplicate_variant => "duplicate variant",
        .duplicate_error_variant => "duplicate error variant",
        .tuple_index_out_of_bounds => "tuple field index out of bounds",
        .struct_field_count_mismatch => "struct literal has wrong number of fields",
        .struct_field_name_mismatch => "struct literal has incorrect field name",
        .struct_field_type_mismatch => "struct field has incorrect type",
        .struct_missing_field => "struct literal missing required field",
        .unknown_struct_field => "unknown struct field",
        .unknown_tuple_field => "unknown tuple field",
        .unknown_module_field => "member `{s}` not found in module/file",
        .expected_pattern_on_decl_lhs => "lhs of decl should be a pattern",
        .missing_field_name_in_struct_literal => "missing field name in struct literal",

        // Variants
        .unknown_enum_tag => "unknown enum tag",
        .unknown_variant_tag => "unknown variant tag",
        .enum_tag_type_mismatch => "enum tag does not belong to the target enum type",
        .variant_payload_arity_mismatch => "variant payload arity mismatch",
        .variant_payload_field_mismatch => "variant payload fields mismatch",
        .variant_payload_field_type_mismatch => "variant payload field type mismatch",
        .variant_payload_field_requires_non_null => "variant payload field requires non-null value",

        // Unions
        .union_literal_multiple_fields => "union literal must specify exactly one field",
        .union_field_type_mismatch => "union field value has incorrect type",
        .unknown_union_field => "unknown union field",
        .union_empty_literal => "union literal must specify a field",
        .union_field_requires_non_null => "union field requires non-null value",

        // Errors / optionals / purity
        .unknown_error_tag => "unknown error tag",
        .error_assigned_to_non_error_union => "cannot assign an error to a non error-union type",
        .invalid_use_of_orelse_on_non_optional => "'orelse' used on a non-optional/non-error value",
        .orelse_type_mismatch => "'orelse' default value type mismatch",
        .catch_on_non_error => "'catch' used on a non error-union value",
        .catch_handler_type_mismatch => "'catch' handler result type mismatch",
        .invalid_optional_unwrap_target => "optional unwrap '?' used on a non-optional",
        .error_propagation_on_non_error => "error propagation '!' used on a non error-union",
        .error_propagation_mismatched_function_result => "error propagation '!' in function with non error-union result",
        .purity_violation => "pure function violated purity constraints",
        .struct_field_requires_non_null => "struct field requires a non-null value",
        .assign_null_to_non_optional => "cannot assign null to a non-optional value",

        // Pointers
        .pointer_type_mismatch => "pointer type mismatch",
        .deref_non_pointer => "cannot dereference a non-pointer",
        .pointer_constness_violation => "cannot assign a *const pointer to a mutable * pointer",

        // Calls
        .wrong_arity_in_call => "wrong number of arguments in function call",
        .argument_type_mismatch => "expected argument of type '{s}', found '{s}'",
        .call_non_callable => "attempted to call a non-callable value",
        .argument_count_mismatch => "argument count does not match parameter count",
        .null_to_non_optional_param => "null passed to a non-optional parameter",

        // Names
        .undefined_identifier => "use of undefined identifier",
        .unknown_function => "unknown function",

        // Specific variants for vague parser situations
        .unexpected_after_expression => "unexpected token after expression: {s}",
        .expected_comma_or_rparen => "expected ',' or ')', found {s}",
        .expected_colon_or_comma_in_param => "expected ':' (type) or ',' (next parameter), found {s}",

        .mlir_verification_failed => "MLIR verification failed: {s}",
        .mlir_block_not_a_type => "MLIR block is not a type",
        .mlir_parse_error => "failed to parse inline MLIR block: {s}",
        .mlir_splice_unknown_identifier => "unknown '@{s}' splice",
        .mlir_splice_not_comptime => "'@{s}' must name a comptime value or type",
        .mlir_splice_unbound => "no comptime binding available for '@{s}'",

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
        .unused_param => "unused parameter '{s}' is never used",
        .unused_variable => "unused local variable is never used",
    };
}

pub const NoteCode = enum {
    unexpected_token_here, // no payload
    expected_identifier_or_keyword, // no payload
    did_you_mean_equal, // no payload
    token_cannot_start_expression, // no payload
    operator_cannot_be_used_here, // no payload
    expected_field_name_or_index_note, // no payload
    separate_parameters, // no payload
    labeled_loops, // no payload
    use_literal_constant_or_binding, // no payload
    use_literal_constant_or_simple_binding, // no payload
    use_single_identifier, // no payload
    provide_element_type_last, // no payload
    attribute_names_identifiers_or_keywords, // no payload
    expected_map_type_or_literal_continuation_note, // no payload
    expected_array_type_or_literal_continuation, // no payload
    attribute_values_literals_or_identifiers, // no payload
    use_extern_async_proc_or_fn, // no payload
    use_extern_proc_fn_or_type, // no payload
    use_colon_for_type_or_comma_or_paren, // no payload
    token_cannot_start_pattern, // no payload

    // New, more actionable note variants (with lightweight payload)
    expected_token_note, // payload: one (expected tag)
    found_token_note, // payload: one (found tag)
    try_inserting_token, // payload: one (token to insert)
    this_token_starts_new_stmt, // payload: one (token)
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

        // New variants (payload-driven)
        .expected_token_note => "expected token: {s}",
        .found_token_note => "found token: {s}",
        .try_inserting_token => "try inserting: {s}",
        .this_token_starts_new_stmt => "this token starts a new statement: {s}",
    };
}

pub const Note = struct {
    loc: ?Loc = null,
    code: NoteCode,
    payload: MessagePayload = .none,
};

pub const Message = struct {
    severity: Severity,
    loc: Loc,
    code: DiagnosticCode,
    payload: MessagePayload,
    notes: std.array_list.Managed(Note),
};

pub const Diagnostics = struct {
    allocator: std.mem.Allocator,
    messages: std.array_list.Managed(Message),
    mutex: std.Thread.Mutex = .{},

    pub fn init(allocator: std.mem.Allocator) Diagnostics {
        return .{ .allocator = allocator, .messages = std.array_list.Managed(Message).init(allocator) };
    }

    pub fn deinit(self: *Diagnostics) void {
        for (self.messages.items) |*m| {
            m.notes.deinit();
        }
        self.messages.deinit();
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
            if (@TypeOf(args[0]) == []const u8)
                return .{ .string = args[0] };
            const f0 = info.fields[0];
            return .{ .one = .{ .a = convertToPayloadTag(@field(args, f0.name)) } };
        } else if (n == 2) {
            const f0 = info.fields[0];
            const f1 = info.fields[1];
            return .{ .two = .{
                .a = convertToPayloadTag(@field(args, f0.name)),
                .b = convertToPayloadTag(@field(args, f1.name)),
            } };
        } else if (n == 3) {
            const f0 = info.fields[0];
            const f1 = info.fields[1];
            const f2 = info.fields[2];
            return .{ .three = .{
                .a = convertToPayloadTag(@field(args, f0.name)),
                .b = convertToPayloadTag(@field(args, f1.name)),
                .c = convertToPayloadTag(@field(args, f2.name)),
            } };
        } else {
            @compileError("Diagnostics.addMessage supports up to 3 payload items (Tag)");
        }
    }

    fn addMessage(self: *Diagnostics, sev: Severity, loc: Loc, comptime code: DiagnosticCode, args: anytype) !void {
        self.mutex.lock();
        defer self.mutex.unlock();

        const info = @typeInfo(@TypeOf(args)).@"struct";
        const arg_count = info.fields.len;
        const payload: MessagePayload = if (arg_count == 0) .none else payloadFromArgs(args);

        // De-duplication check
        for (self.messages.items) |m| {
            if (m.severity == sev and m.code == code and std.meta.eql(m.loc, loc) and std.meta.eql(m.payload, payload)) {
                return;
            }
        }

        const notes = std.array_list.Managed(Note).init(self.allocator);
        try self.messages.append(.{
            .severity = sev,
            .loc = loc,
            .code = code,
            .payload = payload,
            .notes = notes,
        });
    }

    /// Back-compat: simple attachNote without payload.
    pub fn attachNote(self: *Diagnostics, idx: usize, loc: ?Loc, comptime code: NoteCode) !void {
        self.mutex.lock();
        defer self.mutex.unlock();
        if (idx >= self.messages.items.len) return;
        try self.messages.items[idx].notes.append(.{ .loc = loc, .code = code, .payload = .none });
    }

    /// New: attach a note with lightweight payload (Tag values)
    pub fn attachNoteArgs(self: *Diagnostics, idx: usize, loc: ?Loc, comptime code: NoteCode, args: anytype) !void {
        self.mutex.lock();
        defer self.mutex.unlock();
        if (idx >= self.messages.items.len) return;
        const payload = payloadFromArgs(args);
        try self.messages.items[idx].notes.append(.{ .loc = loc, .code = code, .payload = payload });
    }

    pub fn anyErrors(self: *Diagnostics) bool {
        for (self.messages.items) |m| if (m.severity == .err) return true;
        return false;
    }

    pub fn anyWarnings(self: *Diagnostics) bool {
        for (self.messages.items) |m| if (m.severity == .warn) return true;
        return false;
    }

    pub fn count(self: *Diagnostics) usize {
        return self.messages.items.len;
    }

    pub fn messageToOwnedSlice(_: *Diagnostics, allocator: std.mem.Allocator, message: Message) ![]u8 {
        var buffer: std.ArrayList(u8) = .empty;
        defer buffer.deinit(allocator);
        try writeInterpolated(buffer.writer(allocator), diagnosticMessageFmt(message.code), message.payload);
        return buffer.toOwnedSlice(allocator);
    }

    pub fn noteToOwnedSlice(_: *Diagnostics, allocator: std.mem.Allocator, note: Note) ![]u8 {
        var buffer: std.ArrayList(u8) = .empty;
        defer buffer.deinit(allocator);
        try writeInterpolated(buffer.writer(allocator), diagnosticNoteFmt(note.code), note.payload);
        return buffer.toOwnedSlice(allocator);
    }

    // Pretty-print diagnostics with source excerpt and caret span (unstyled)
    pub fn emit(self: *Diagnostics, context: *Context, writer: anytype) !void {
        try self.emitStyled(context, writer, true);
    }

    // Pretty-print diagnostics Rust-like with optional ANSI colors
    pub fn emitStyled(self: *Diagnostics, context: *Context, writer: anytype, color: bool) !void {
        const max_errors_to_show = 20;
        var error_count: usize = 0;
        for (self.messages.items) |m| {
            if (m.severity == .err) {
                error_count += 1;
            }
        }

        var source_map = std.AutoArrayHashMap(usize, []const u8).init(context.gpa);
        defer source_map.deinit();

        var errors_shown: usize = 0;
        for (self.messages.items) |m| {
            if (errors_shown >= max_errors_to_show) {
                // Stop printing after reaching the error limit.
                break;
            }

            const sev_str = switch (m.severity) {
                .err => "error",
                .warning => "warning",
                .note => "note",
            };
            const sev_col = switch (m.severity) {
                .err => Colors.red,
                .warning => Colors.yellow,
                .note => Colors.blue,
            };
            // Source location
            const src = source_map.get(m.loc.file_id) orelse blk: {
                const data = try context.source_manager.read(m.loc.file_id);
                try source_map.put(m.loc.file_id, data);
                break :blk data;
            };
            const filename = context.source_manager.get(m.loc.file_id) orelse "unknown";

            // Location line
            const lc = lineCol(src, m.loc.start);
            try writer.print("{s}{s}{s}:{d}:{d}: ", .{
                if (color) Colors.cyan else "",
                filename,
                if (color) Colors.reset else "",
                lc.line + 1,
                lc.col + 1,
            });

            // Header: error[code]: message (with payload)
            try writer.print("{s}{s}{s}: {s}{s}", .{
                if (color) Colors.bold else "",
                if (color) sev_col else "",
                sev_str,
                if (color) Colors.reset else "",
                if (color) Colors.bold else "",
            });
            try writeInterpolated(writer, diagnosticMessageFmt(m.code), m.payload);
            if (color) try writer.print("{s}", .{Colors.reset});

            const line_no = lc.line + 1;
            const width = digits(line_no);
            // Gutter spacer
            // try writer.print("\n {s}{s}▌{s}\n", .{ gutterPad(width), if (color) Colors.cyan else "", if (color) Colors.reset else "" });
            try writer.print("\n", .{});
            // Source line
            const line_slice = src[lc.line_start..lc.line_end];
            const num_pad = numPad(width, line_no);
            try writer.print("{s}{d} {s}▌{s} {s}\n", .{ num_pad, line_no, Colors.cyan, Colors.reset, line_slice });
            // Underline (single-line span)
            const caret_start = lc.col;
            const span = if (m.loc.end > m.loc.start and m.loc.end <= lc.line_end) (m.loc.end - m.loc.start) else 1;
            try writer.print(" {s}{s}▌{s} ", .{ gutterPad(width), Colors.cyan, Colors.reset });
            var i: usize = 0;
            while (i < caret_start) : (i += 1) try writer.print(" ", .{});
            if (color) try writer.print("{s}", .{sev_col});
            i = 0;
            while (i < span) : (i += 1) try writer.print("^", .{});
            if (color) try writer.print("{s}", .{Colors.reset});
            try writer.print("\n", .{});

            // Notes (with optional secondary locations)
            for (m.notes.items) |n| {
                if (n.loc) |nl| {
                    const nlc = lineCol(src, nl.start);
                    try writer.print(" {s}= {s}note[{s}]{s}: ", .{ gutterPad(width), if (color) Colors.blue else "", @tagName(n.code), if (color) Colors.reset else "" });
                    try writeInterpolated(writer, diagnosticNoteFmt(n.code), n.payload);
                    try writer.print(" (at {s}{d}:{d}{s})\n", .{ if (color) Colors.cyan else "", nlc.line + 1, nlc.col + 1, if (color) Colors.reset else "" });
                } else {
                    try writer.print(" {s}= {s}note[{s}]{s}: ", .{ gutterPad(width), if (color) Colors.blue else "", @tagName(n.code), if (color) Colors.reset else "" });
                    try writeInterpolated(writer, diagnosticNoteFmt(n.code), n.payload);
                    try writer.print("\n", .{});
                }
            }

            try writer.print("\n", .{});

            if (m.severity == .err) {
                errors_shown += 1;
            }
        }

        if (error_count > errors_shown) {
            const remaining = error_count - errors_shown;
            try writer.print("\n... and {d} more error(s) not shown.\n", .{remaining});
        }

        try writer.flush();
    }

    fn writeInterpolated(writer: anytype, fmt: []const u8, payload: MessagePayload) !void {
        var args: [3][]const u8 = .{ "", "", "" };
        var arg_count: usize = 0;
        switch (payload) {
            .none => {},
            .string => |s| {
                args[0] = s;
                arg_count = 1;
            },
            .one => |p| {
                args[0] = @tagName(p.a);
                arg_count = 1;
            },
            .two => |p| {
                args[0] = @tagName(p.a);
                args[1] = @tagName(p.b);
                arg_count = 2;
            },
            .three => |p| {
                args[0] = @tagName(p.a);
                args[1] = @tagName(p.b);
                args[2] = @tagName(p.c);
                arg_count = 3;
            },
        }

        var used: usize = 0;
        var i: usize = 0;
        while (i < fmt.len) {
            if (i + 2 < fmt.len and fmt[i] == '{' and fmt[i + 1] == 's' and fmt[i + 2] == '}') {
                if (used < arg_count) {
                    try writer.print("{s}", .{args[used]});
                    used += 1;
                } else {
                    try writer.writeAll("{s}");
                }
                i += 3;
            } else {
                try writer.print("{c}", .{fmt[i]});
                i += 1;
            }
        }
    }

    // (Old helper retained for reference; no longer used)
    fn printMessage(writer: anytype, comptime fmt: []const u8, payload: MessagePayload) !void {
        switch (payload) {
            .none => try writer.print("{s}", .{fmt}),
            .one => |p| try writer.print(fmt, .{@tagName(p.a)}),
            .two => |p| try writer.print(fmt, .{ @tagName(p.a), @tagName(p.b) }),
            .three => |p| try writer.print(fmt, .{ @tagName(p.a), @tagName(p.b), @tagName(p.c) }),
        }
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
        // find end of line
        var end: usize = idx;
        while (end < src.len and src[end] != '\n' and src[end] != '\r') : (end += 1) {}
        return .{ .line = line, .col = idx - last_nl, .line_start = last_nl, .line_end = end };
    }

    fn digits(n: usize) usize {
        var v: usize = n;
        var c: usize = 1;
        while (v >= 10) : (v /= 10) c += 1;
        return c;
    }

    fn gutterPad(width: usize) []const u8 {
        // Return a short run of spaces for gutter alignment (max 16)
        const max = 16;
        const n = if (width > max) max else width;
        return space_buf[0..n];
    }

    const space_buf = [_]u8{' '} ** 16;

    fn numPad(width: usize, n: usize) []const u8 {
        const d = digits(n);
        const pad = if (width > d) width - d else 0;
        return gutterPad(pad);
    }

    const Colors = struct {
        pub const reset = "\x1b[0m";
        pub const bold = "\x1b[1m";
        pub const red = "\x1b[31m";
        pub const yellow = "\x1b[33m";
        pub const blue = "\x1b[34m";
        pub const cyan = "\x1b[36m";
    };
};
