module magnitude_comparator_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic eq,
    input logic gt
);

    // eq must match the equality comparison of a and b.
    check_eq_matches_comparison: assert property (
        @(posedge clk) eq == (a == b)
    );

    // gt must match the greater-than comparison of a and b.
    check_gt_matches_comparison: assert property (
        @(posedge clk) gt == (a > b)
    );

    // eq and gt cannot both be asserted at the same time.
    check_eq_gt_mutex: assert property (
        @(posedge clk) !(eq && gt)
    );

    // When a is less than b, neither eq nor gt may be asserted.
    check_lt_case_outputs: assert property (
        @(posedge clk) (a < b) |-> (!eq && !gt)
    );

    // If eq is asserted, the inputs must be equal.
    check_eq_implies_equal_inputs: assert property (
        @(posedge clk) eq |-> (a == b)
    );

    // If gt is asserted, a must be greater than b.
    check_gt_implies_input_order: assert property (
        @(posedge clk) gt |-> (a > b)
    );

endmodule