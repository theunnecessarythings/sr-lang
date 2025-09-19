const std = @import("std");
const Loc = @import("lexer.zig").Token.Loc;
const Tag = @import("lexer.zig").Token.Tag;

pub const Severity = enum {
    err,
    warning,
    note,
};

pub const DiagnosticCode = enum {
    unexpected_token,
    expected_identifier,
    expected_type_in_declaration,
    unexpected_token_in_expression,
    unexpected_postfix_operator,
    expected_field_name_or_index,
    expected_closure_param_separator,
    expected_loop_after_label,
    underscore_not_const_in_range_pattern,
    left_side_not_const_like_in_range_pattern,
    invalid_binding_name_in_at_pattern,
    unexpected_token_in_pattern,
    tensor_missing_arguments,
    expected_attribute_name,
    expected_map_type_or_literal_continuation,
    expected_array_like_continuation,
    expected_attribute_value,
    expected_extern_async_function,
    expected_extern_declaration,
    expected_parameter_type_or_end,
    checker_insert_not_expanded,
    return_outside_function,
    return_value_in_void_function,
    missing_return_value,
    break_outside_loop,
    continue_outside_loop,
    defer_outside_function,
    errdefer_outside_function,
    checker_comptime_not_executed,
    checker_code_block_not_executed,
    array_size_not_integer_literal,
    duplicate_field,
    duplicate_enum_field,
    enum_discriminant_not_integer,
    duplicate_variant,
    duplicate_error_variant,
    simd_lanes_not_integer_literal,
    tensor_dimension_not_integer_literal,
    division_by_zero,
    invalid_binary_op_operands,
    invalid_unary_op_operand,

    could_not_resolve_type,
    // Specific diagnostics used by tests
    return_type_mismatch,
    non_boolean_condition,
    if_expression_requires_else,
    if_branch_type_mismatch,
    while_expression_not_value,
    pattern_shape_mismatch,
    non_iterable_in_for,
    tuple_arity_mismatch,
    struct_pattern_field_mismatch,
    variant_payload_mismatch,
    non_exhaustive_match,
    overlapping_match_arm,
    unreachable_match_arm,
    errdefer_in_non_error_function,
    loop_break_value_type_conflict,
    assignment_type_mismatch,
    unreachable_code_after_break,
    await_non_async,
    await_type_mismatch,
    await_outside_async_context,
    cast_target_not_type,
    invalid_bitcast,
    invalid_checked_cast,
    invalid_import_operand,
    // Additional specific diagnostics used in tests
    heterogeneous_array_elements,
    array_length_mismatch,
    tuple_index_out_of_bounds,
    map_mixed_key_types,
    map_mixed_value_types,
    ambiguous_empty_map,
    type_annotation_mismatch,
    map_wrong_key_type,
    non_integer_index,
    not_indexable,
    assign_null_to_non_optional,
    struct_field_type_mismatch,
    struct_missing_field,
    unknown_struct_field,
    unknown_enum_tag,
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
    pointer_type_mismatch,
    deref_non_pointer,
    pointer_constness_violation,
    simd_invalid_element_type,
    tensor_missing_element_type,
    type_value_mismatch,
    noreturn_not_storable,
    wrong_arity_in_call,
    argument_type_mismatch,
    call_non_callable,
    null_to_non_optional_param,
    undefined_identifier,
    field_access_on_non_aggregate,
    invalid_struct_field_index,
    invalid_use_of_orelse_on_non_optional,
    orelse_type_mismatch,
    catch_on_non_error,
    catch_handler_type_mismatch,
    invalid_optional_unwrap_target,
    error_propagation_on_non_error,
    error_propagation_mismatched_function_result,
    purity_violation,
    struct_field_requires_non_null,
    invalid_index_type,
    argument_count_mismatch,
    unknown_function,
};

pub fn diagnosticMessageFmt(code: DiagnosticCode) []const u8 {
    return switch (code) {
        .unexpected_token => "unexpected token: {s}",
        .expected_identifier => "expected identifier, found {s}",
        .expected_type_in_declaration => "expected '=' or '::' after type in declaration, found {s}",
        .unexpected_token_in_expression => "unexpected token in expression: {s}",
        .unexpected_postfix_operator => "unexpected postfix operator: {s}",
        .expected_field_name_or_index => "expected identifier or integer after '.', found {s}",
        .expected_closure_param_separator => "expected ',' or '|' after closure parameter, found {s}",
        .expected_loop_after_label => "expected 'for' or 'while' after label, found {s}",
        .underscore_not_const_in_range_pattern => "'_' is not valid as a constant in a range pattern",
        .left_side_not_const_like_in_range_pattern => "left side of a range pattern must be const-like",
        .invalid_binding_name_in_at_pattern => "only simple identifier paths can be used as binding names in '@' patterns",
        .unexpected_token_in_pattern => "unexpected token in pattern: {s}",
        .tensor_missing_arguments => "expected at least one argument to 'tensor', found none",
        .expected_attribute_name => "expected attribute name, found {s}",
        .expected_map_type_or_literal_continuation => "expected ']' or ',' in map type/literal, found {s}",
        .expected_array_like_continuation => "expected ']', ':', or ',' in array-like, found {s}",
        .expected_attribute_value => "expected literal or identifier after '=', found {s}",
        .expected_extern_async_function => "expected 'proc' or 'fn' after 'extern async', found {s}",
        .expected_extern_declaration => "expected 'proc', 'fn', or a type after 'extern', found {s}",
        .expected_parameter_type_or_end => "expected ':', ',', or ')' after parameter, found {s}",
        .checker_insert_not_expanded => "checker_v2: insert not expanded yet; walking only",
        .return_outside_function => "'return' used outside of a function",
        .return_value_in_void_function => "return with a value in a void function",
        .missing_return_value => "missing return value",
        .break_outside_loop => "'break' used outside of a loop",
        .continue_outside_loop => "'continue' used outside of a loop",
        .defer_outside_function => "'defer' only valid inside a function",
        .errdefer_outside_function => "'errdefer' only valid inside a function",
        .checker_comptime_not_executed => "checker_v2: comptime not executed; walking only",
        .checker_code_block_not_executed => "checker_v2: code block not executed; walking only",
        .array_size_not_integer_literal => "array size must be an integer literal",
        .duplicate_field => "duplicate field",
        .duplicate_enum_field => "duplicate enum field",
        .enum_discriminant_not_integer => "enum discriminant should be an integer literal",
        .duplicate_variant => "duplicate variant",
        .duplicate_error_variant => "duplicate error variant",
        .simd_lanes_not_integer_literal => "SIMD lanes must be an integer literal",
        .tensor_dimension_not_integer_literal => "tensor dimension must be an integer literal",
        .division_by_zero => "division by zero",
        .invalid_binary_op_operands => "invalid operands for binary operator '{s}': '{s}' and '{s}'",
        .invalid_unary_op_operand => "invalid operand for unary operator '{s}': '{s}'",
        .could_not_resolve_type => "could not resolve type: {s}",
        .return_type_mismatch => "return type does not match function result type",
        .non_boolean_condition => "condition expression is not boolean",
        .if_expression_requires_else => "'if' used as an expression must have an 'else' branch",
        .if_branch_type_mismatch => "'if' branches produce mismatched types",
        .while_expression_not_value => "'while' cannot be used as a value (no resulting expression)",
        .pattern_shape_mismatch => "pattern does not match the shape of the value",
        .non_iterable_in_for => "value is not iterable in 'for' loop",
        .tuple_arity_mismatch => "tuple pattern arity does not match value",
        .struct_pattern_field_mismatch => "struct pattern fields do not match value",
        .variant_payload_mismatch => "variant pattern payload does not match",
        .non_exhaustive_match => "non-exhaustive match; missing cases",
        .overlapping_match_arm => "overlapping or duplicate match arm",
        .unreachable_match_arm => "unreachable match arm (covered by previous arms)",
        .errdefer_in_non_error_function => "'errdefer' only valid in functions returning an error union",
        .loop_break_value_type_conflict => "loop break values have conflicting types",
        .assignment_type_mismatch => "assigned value does not match the variable's type",
        .unreachable_code_after_break => "unreachable code after an unconditional break",
        .await_non_async => "'await' applied to a non-async expression",
        .await_type_mismatch => "awaited expression type does not match expected type",
        .await_outside_async_context => "'await' used outside of an async context",
        .cast_target_not_type => "cast target is not a type",
        .invalid_bitcast => "invalid bitcast between incompatible types",
        .invalid_checked_cast => "checked cast cannot succeed",
        .invalid_import_operand => "invalid import operand; expected string-like path",
        .heterogeneous_array_elements => "array elements must have a uniform type",
        .array_length_mismatch => "array literal length does not match declared size",
        .tuple_index_out_of_bounds => "tuple field index out of bounds",
        .map_mixed_key_types => "map literal has mixed key types",
        .map_mixed_value_types => "map literal has mixed value types",
        .ambiguous_empty_map => "empty map literal is ambiguous without a type annotation",
        .type_annotation_mismatch => "initializer does not match the annotated type",
        .map_wrong_key_type => "map index has wrong key type",
        .non_integer_index => "array index must be an integer",
        .not_indexable => "value is not indexable",
        .assign_null_to_non_optional => "cannot assign null to a non-optional",
        .struct_field_type_mismatch => "struct field has incorrect type",
        .struct_missing_field => "struct literal missing required field",
        .unknown_struct_field => "unknown struct field",
        .unknown_enum_tag => "unknown enum tag",
        .enum_tag_type_mismatch => "enum tag does not belong to the target enum type",
        .variant_payload_arity_mismatch => "variant payload arity mismatch",
        .variant_payload_field_mismatch => "variant payload fields mismatch",
        .variant_payload_field_type_mismatch => "variant payload field type mismatch",
        .variant_payload_field_requires_non_null => "variant payload field requires non-null value",
        .union_literal_multiple_fields => "union literal must specify exactly one field",
        .union_field_type_mismatch => "union field value has incorrect type",
        .unknown_union_field => "unknown union field",
        .union_empty_literal => "union literal must specify a field",
        .union_field_requires_non_null => "union field requires non-null value",
        .unknown_error_tag => "unknown error tag",
        .error_assigned_to_non_error_union => "cannot assign an error to a non error-union type",
        .pointer_type_mismatch => "pointer type mismatch",
        .deref_non_pointer => "cannot dereference a non-pointer",
        .pointer_constness_violation => "cannot assign a *const pointer to a mutable * pointer",
        .simd_invalid_element_type => "invalid SIMD element type",
        .tensor_missing_element_type => "tensor is missing the element type",
        .type_value_mismatch => "value is not a type",
        .noreturn_not_storable => "'noreturn' is not a storable value type",
        .wrong_arity_in_call => "wrong number of arguments in function call",
        .argument_type_mismatch => "argument type does not match parameter type",
        .call_non_callable => "attempted to call a non-callable value",
        .null_to_non_optional_param => "null passed to a non-optional parameter",
        .undefined_identifier => "use of undefined identifier",
        .field_access_on_non_aggregate => "field access on non-aggregate value",
        .invalid_struct_field_index => "numeric field access is invalid on a struct",
        .invalid_use_of_orelse_on_non_optional => "'orelse' used on a non-optional/non-error value",
        .orelse_type_mismatch => "'orelse' default value type mismatch",
        .catch_on_non_error => "'catch' used on a non error-union value",
        .catch_handler_type_mismatch => "'catch' handler result type mismatch",
        .invalid_optional_unwrap_target => "optional unwrap '?' used on a non-optional",
        .error_propagation_on_non_error => "error propagation '!' used on a non error-union",
        .error_propagation_mismatched_function_result => "error propagation '!' in function with non error-union result",
        .purity_violation => "pure function violated purity constraints",
        .struct_field_requires_non_null => "struct field requires a non-null value",
        .invalid_index_type => "invalid index type",
        .argument_count_mismatch => "argument count does not match parameter count",
        .unknown_function => "unknown function",
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
    token_cannot_start_pattern,
    provide_element_type_last,
    attribute_names_identifiers_or_keywords,
    expected_map_type_or_literal_continuation_note,
    expected_array_type_or_literal_continuation,
    attribute_values_literals_or_identifiers,
    use_extern_async_proc_or_fn,
    use_extern_proc_fn_or_type,
    use_colon_for_type_or_comma_or_paren,
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
        .labeled_loops => "labeled loops: label: for ... {{ ... }} or label: while ... {{ ... }}",
        .use_literal_constant_or_binding => "use a literal, constant path, or a binding name",
        .use_literal_constant_or_simple_binding => "use a literal, constant path, or a simple binding",
        .use_single_identifier => "use a single identifier without dots",
        .token_cannot_start_pattern => "this token cannot start a pattern",
        .provide_element_type_last => "provide the element type as the last argument, and shape dimensions before it",
        .attribute_names_identifiers_or_keywords => "attribute names can be identifiers or keywords",
        .expected_map_type_or_literal_continuation_note => "use ']' to end a map type or ',' to separate key-value pairs in a map literal",
        .expected_array_type_or_literal_continuation => "use ']' to end an array type or literal, ':' for a map type/literal, or ',' to separate elements in an array literal",
        .attribute_values_literals_or_identifiers => "attribute values must be literals or identifiers",
        .use_extern_async_proc_or_fn => "use 'extern async proc' or 'extern async fn'",
        .use_extern_proc_fn_or_type => "use 'extern proc', 'extern fn', or 'extern struct/enum/union'",
        .use_colon_for_type_or_comma_or_paren => "use ':' to specify a type, or ',' / ')' to end the parameter",
    };
}

pub const Note = struct {
    loc: ?Loc = null,
    code: NoteCode,
};

const MessagePayload = union(enum) {
    none,
    one: struct { Tag },
    two: struct { Tag, Tag },
    three: struct { Tag, Tag, Tag },
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

    fn addMessage(self: *Diagnostics, sev: Severity, loc: Loc, comptime code: DiagnosticCode, args: anytype) !void {
        const notes = std.array_list.Managed(Note).init(self.allocator);
        // check args count and create payload
        const arg_count = @typeInfo(@TypeOf(args)).@"struct".fields.len;
        if (arg_count == 0) {
            // no args
            try self.messages.append(.{
                .severity = sev,
                .loc = loc,
                .code = code,
                .payload = .none,
                .notes = notes,
            });
            return;
        } else if (arg_count == 1) {
            try self.messages.append(.{
                .severity = sev,
                .loc = loc,
                .code = code,
                .payload = .{ .one = args },
                .notes = notes,
            });
            return;
        } else if (arg_count == 2) {
            try self.messages.append(.{
                .severity = sev,
                .loc = loc,
                .code = code,
                .payload = .{ .two = args },
                .notes = notes,
            });
            return;
        } else if (arg_count == 3) {
            try self.messages.append(.{
                .severity = sev,
                .loc = loc,
                .code = code,
                .payload = .{ .three = args },
                .notes = notes,
            });
            return;
        } else {
            // too many args
            return error.TooManyArguments;
        }

        try self.messages.append(.{
            .severity = sev,
            .loc = loc,
            .code = code,
            .payload = args,
            .notes = notes,
        });
    }

    pub fn attachNote(self: *Diagnostics, idx: usize, loc: ?Loc, comptime code: NoteCode) !void {
        if (idx >= self.messages.items.len) return;
        try self.messages.items[idx].notes.append(.{ .loc = loc, .code = code });
    }

    pub fn anyErrors(self: *Diagnostics) bool {
        for (self.messages.items) |m| if (m.severity == .err) return true;
        return false;
    }

    pub fn count(self: *Diagnostics) usize {
        return self.messages.items.len;
    }

    // Pretty-print diagnostics with source excerpt and caret span (unstyled)
    pub fn emit(self: *Diagnostics, source: []const u8, writer: anytype, filename: []const u8) !void {
        try self.emitStyled(source, writer, filename, true);
    }

    // Pretty-print diagnostics Rust-like with optional ANSI colors
    pub fn emitStyled(self: *Diagnostics, source: []const u8, writer: anytype, filename: []const u8, color: bool) !void {
        for (self.messages.items) |m| {
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
            // Header: error: message
            try writer.print("{s}{s}{s}{s}: {s}{s}\n", .{
                if (color) Colors.bold else "",
                if (color) sev_col else "",
                sev_str,
                if (color) Colors.reset else "",
                if (color) Colors.bold else "",
                m.message,
            });

            // Location line
            const lc = lineCol(source, m.loc.start);
            try writer.print(" {s}--> {s}{s}{s}:{d}:{d}\n", .{
                gutterPad(0),
                if (color) Colors.cyan else "",
                filename,
                if (color) Colors.reset else "",
                lc.line + 1,
                lc.col + 1,
            });

            const line_no = lc.line + 1;
            const width = digits(line_no);
            // Gutter spacer
            try writer.print(
                " {s}{s}▌{s}\n",
                .{ gutterPad(width), if (color) Colors.cyan else "", if (color) Colors.reset else "" },
            );
            // Source line
            const line_slice = source[lc.line_start..lc.line_end];
            const num_pad = numPad(width, line_no);
            try writer.print(
                "{s}{d} {s}▌{s} {s}\n",
                .{ num_pad, line_no, Colors.cyan, Colors.reset, line_slice },
            );
            // Underline
            const caret_start = lc.col;
            const span = if (m.loc.end > m.loc.start and m.loc.end <= lc.line_end) (m.loc.end - m.loc.start) else 1;
            try writer.print(
                " {s}{s}▌{s} ",
                .{ gutterPad(width), Colors.cyan, Colors.reset },
            );
            var i: usize = 0;
            while (i < caret_start) : (i += 1) try writer.print(" ", .{{}});
            if (color) try writer.print("{s}", .{sev_col});
            i = 0;
            while (i < span) : (i += 1) try writer.print("^", .{{}});
            if (color) try writer.print("{s}", .{Colors.reset});
            try writer.print("\n", .{{}});

            // Notes
            for (m.notes.items) |n| {
                if (n.loc) |nl| {
                    const nlc = lineCol(source, nl.start);
                    try writer.print(" {s}= {s}note{s}: {s} (at {s}{d}:{d}{s})\n", .{
                        gutterPad(width),
                        if (color) Colors.blue else "",
                        if (color) Colors.reset else "",
                        n.message,
                        if (color) Colors.cyan else "",
                        nlc.line + 1,
                        nlc.col + 1,
                        if (color) Colors.reset else "",
                    });
                } else {
                    try writer.print(" {s}= {s}note{s}: {s}\n", .{
                        gutterPad(width),
                        if (color) Colors.blue else "",
                        if (color) Colors.reset else "",
                        n.message,
                    });
                }
            }

            try writer.print("\n", .{{}});
        }
        try writer.flush();
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
