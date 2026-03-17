module magnitude_comparison_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic eq,
    input logic gt
);

    // eq matches the equality comparison of A and B.
    check_eq_function: assert property (
        @(posedge clk) eq === (A == B)
    );

    // gt matches the greater-than comparison of A and B.
    check_gt_function: assert property (
        @(posedge clk) gt === (A > B)
    );

    // Equal inputs drive eq high and gt low.
    check_equal_case: assert property (
        @(posedge clk) (A == B) |-> (eq && !gt)
    );

    // A greater than B drives gt high and eq low.
    check_greater_case: assert property (
        @(posedge clk) (A > B) |-> (gt && !eq)
    );

    // A less than B drives both outputs low.
    check_less_case: assert property (
        @(posedge clk) (A < B) |-> (!eq && !gt)
    );

    // eq and gt are never asserted at the same time.
    check_outputs_mutex: assert property (
        @(posedge clk) !(eq && gt)
    );

endmodule