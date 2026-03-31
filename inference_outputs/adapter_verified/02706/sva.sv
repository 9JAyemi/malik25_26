module magnitude_comparator_selector_sva (
    input logic clk,
    input logic [2:0] a,
    input logic [2:0] b,
    input logic [1:0] select,
    input logic [2:0] comparison_result,
    input logic [1:0] input_selected
);

// When a > b, comparison_result equals a and input_selected is 00.
    check_select_a_when_a_gt_b: assert property (
        @(posedge clk) (a > b) |-> (comparison_result == a) && (input_selected == 2'b00)
    );

// When b > a, comparison_result equals b and input_selected is 01.
    check_select_b_when_b_gt_a: assert property (
        @(posedge clk) (b > a) |-> (comparison_result == b) && (input_selected == 2'b01)
    );

// When a == b, comparison_result equals a and input_selected equals select.
    check_select_select_when_equal: assert property (
        @(posedge clk) (a == b) |-> (comparison_result == a) && (input_selected == select)
    );

// comparison_result always matches the RTL's selected input.
    check_result_matches_selected_input: assert property (
        @(posedge clk) (comparison_result == ((a > b) ? a : b))
    );

// input_selected is 00 only when a > b.
    check_input_selected_00_only_when_a_gt_b: assert property (
        @(posedge clk) (input_selected == 2'b00) |-> (a > b)
    );

// input_selected is 01 only when b > a.
    check_input_selected_01_only_when_b_gt_a: assert property (
        @(posedge clk) (input_selected == 2'b01) |-> (b > a)
    );

// input_selected is 10 or 11 only when a == b.
    check_input_selected_high_only_when_equal: assert property (
        @(posedge clk) ((input_selected == 2'b10) || (input_selected == 2'b11)) |-> (a == b)
    );

// When a > b, input_selected is 00.
    check_input_selected_00_when_a_gt_b: assert property (
        @(posedge clk) (a > b) |-> (input_selected == 2'b00)
    );

// When b > a, input_selected is 01.
    check_input_selected_01_when_b_gt_a: assert property (
        @(posedge clk) (b > a) |-> (input_selected == 2'b01)
    );

// When a == b, input_selected equals select.
    check_input_selected_matches_select_when_equal: assert property (
        @(posedge clk) (a == b) |-> (input_selected == select)
    );

endmodule
