module magnitude_comparator_selector_sva (
    input logic [2:0] a,
    input logic [2:0] b,
    input logic [1:0] select,
    input logic [2:0] comparison_result,
    input logic [1:0] input_selected
);

    // When a is greater than b, the output selects a.
    check_select_a_when_a_gt_b: assert property (
        @($global_clock)
        (a > b) |-> ((comparison_result == a) && (input_selected == 2'b00))
    );

    // When b is greater than a, the output selects b.
    check_select_b_when_b_gt_a: assert property (
        @($global_clock)
        (b > a) |-> ((comparison_result == b) && (input_selected == 2'b01))
    );

    // When a and b are equal, the output selects a and passes select.
    check_equal_inputs_select_a: assert property (
        @($global_clock)
        (a == b) |-> ((comparison_result == a) && (input_selected == select))
    );

    // The selected input is always 00 or 01.
    check_input_selected_legal_values: assert property (
        @($global_clock)
        (input_selected inside {2'b00, 2'b01})
    );

    // The selected input is never 10 or 11.
    check_input_selected_not_10_or_11: assert property (
        @($global_clock)
        !(input_selected inside {2'b10, 2'b11})
    );

    // The selected input is never 10 or 11.
    check_input_selected_not_10_or_11: assert property (
        @($global_clock)
        !(input_selected inside {2'b10, 2'b11})
    );

    // The selected input is always 00 or 01.
    check_input_selected_legal_values: assert property (
        @($global_clock)
        (input_selected inside {2'b00, 2'b01})
    );

    // The selected input is never 10 or 11.
    check_input_selected_not_10_or_11: assert property (
        @($global_clock)
        !(input_selected inside {2'b10, 2'b11})
    );

    // The selected input is always 00 or 01.
    check_input_selected_legal_values: assert property (
        @($global_clock)
        (input_selected inside {2'b00, 2'b01})
    );

    // The selected input is never 10 or 11.
    check_input_selected_not_10_or_11: assert property (
        @($global_clock)
        !(input_selected inside {2'b10, 2'b11})
    );

endmodule