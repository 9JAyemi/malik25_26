module comparator_sva (
    input logic clk,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic out
);

    // Output is high when A is greater than B.
    check_out_high_when_a_gt_b: assert property (
        @(posedge clk) (A > B) |-> (out == 1'b1)
    );

    // Output is low when A is less than B.
    check_out_low_when_a_lt_b: assert property (
        @(posedge clk) (A < B) |-> (out == 1'b0)
    );

    // Output is low when A equals B.
    check_out_low_when_a_eq_b: assert property (
        @(posedge clk) (A == B) |-> (out == 1'b0)
    );

    // Output always matches the comparison result.
    check_out_matches_comparison: assert property (
        @(posedge clk) out == (A > B)
    );

endmodule