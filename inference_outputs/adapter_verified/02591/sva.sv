module magnitude_comparator_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic out
);

// out must be 1 when the magnitude of A is greater than the magnitude of B.
    check_out_high_when_a_greater: assert property (
        @(posedge clk) (|A > |B) |-> (out == 1'b1)
    );

// out must be 0 when the magnitude of A is less than or equal to the magnitude of B.
    check_out_low_when_a_not_greater: assert property (
        @(posedge clk) (|A <= |B) |-> (out == 1'b0)
    );

// out must match the RTL comparison result.
    check_out_matches_rtl_comparison: assert property (
        @(posedge clk) out == (|A > |B)
    );

endmodule
