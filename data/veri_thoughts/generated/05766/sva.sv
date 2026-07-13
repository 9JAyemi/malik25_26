module comparator_sva (
    input logic       clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       out
);

    // If a is greater than b, out must be high.
    check_a_gt_b_sets_out_high: assert property (
        @(posedge clk) (a > b) |-> (out == 1'b1)
    );

    // If a is less than b, out must be low.
    check_a_lt_b_sets_out_low: assert property (
        @(posedge clk) (a < b) |-> (out == 1'b0)
    );

    // For unequal inputs, out must match the a>b comparison.
    check_unequal_inputs_match_compare: assert property (
        @(posedge clk) (a != b) |-> (out == (a > b))
    );

    // For unequal inputs, a high out implies a is greater than b.
    check_unequal_out_high_implies_a_gt_b: assert property (
        @(posedge clk) ((a != b) && (out == 1'b1)) |-> (a > b)
    );

    // For unequal inputs, a low out implies a is less than b.
    check_unequal_out_low_implies_a_lt_b: assert property (
        @(posedge clk) ((a != b) && (out == 1'b0)) |-> (a < b)
    );

endmodule