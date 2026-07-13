module magnitude_comparator_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic out
);

    // out must match the RTL's comparison of the absolute values of A and B.
    check_out_matches_rtl: assert property (
        @(posedge clk) out == (|A > |B)
    );

    // A with a greater magnitude than B must drive out high.
    check_a_greater_sets_out: assert property (
        @(posedge clk) (|A > |B) |-> (out == 1'b1)
    );

    // A with a lesser or equal magnitude than B must drive out low.
    check_a_not_greater_clears_out: assert property (
        @(posedge clk) !(|A > |B) |-> (out == 1'b0)
    );

    // Equal magnitudes must produce a low output.
    check_equal_magnitudes_clear_out: assert property (
        @(posedge clk) (|A == |B) |-> (out == 1'b0)
    );

endmodule