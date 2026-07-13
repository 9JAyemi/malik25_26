module magnitude_comparator_selector_sva (
    input logic [2:0] a,
    input logic [2:0] b,
    input logic [1:0] select,
    input logic [2:0] comparison_result,
    input logic [1:0] input_selected
);

    // When a is greater than b, the output selects a and uses 00.
    check_a_greater_selects_a: assert property (
        @($global_clock) (a > b) |-> ((comparison_result == a) && (input_selected == 2'b00))
    );

    // When b is greater than a, the output selects b and uses 01.
    check_b_greater_selects_b: assert property (
        @($global_clock) (b > a) |-> ((comparison_result == b) && (input_selected == 2'b01))
    );

    // When a equals b, the output selects a and passes through select.
    check_equal_inputs_select_a: assert property (
        @($global_clock) (a == b) |-> ((comparison_result == a) && (input_selected == select))
    );

    // The output always matches one of the three implemented cases.
    check_output_matches_implemented_cases: assert property (
        @($global_clock)
        ((a > b) && (comparison_result == a) && (input_selected == 2'b00)) ||
        ((b > a) && (comparison_result == b) && (input_selected == 2'b01)) ||
        ((a == b) && (comparison_result == a) && (input_selected == select))
    );

    // The selected input is always either a or b.
    check_selected_input_is_a_or_b: assert property (
        @($global_clock) ((input_selected == 2'b00) || (input_selected == 2'b01))
    );

    // The selected input is never 2'b10 or 2'b11.
    check_selected_input_valid_range: assert property (
        @($global_clock) (input_selected != 2'b10) && (input_selected != 2'b11)
    );

endmodule