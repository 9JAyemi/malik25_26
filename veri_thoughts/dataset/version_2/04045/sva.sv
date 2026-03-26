module comparator_sva (
    input logic clk,
    input logic [2:0] A,
    input logic [2:0] B,
    input logic out
);

    // out must exactly reflect whether A is greater than B.
    check_out_matches_gt_compare: assert property (
        @(posedge clk) (out == (A > B))
    );

    // Greater-than case drives out high.
    check_out_high_when_a_gt_b: assert property (
        @(posedge clk) (A > B) |-> (out == 1'b1)
    );

    // Less-than case drives out low.
    check_out_low_when_a_lt_b: assert property (
        @(posedge clk) (A < B) |-> (out == 1'b0)
    );

    // Equal case drives out low.
    check_out_low_when_a_eq_b: assert property (
        @(posedge clk) (A == B) |-> (out == 1'b0)
    );

endmodule