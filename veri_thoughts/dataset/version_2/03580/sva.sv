module binary_adder_sva (
    input logic [3:0] SUM,
    input logic COUT,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CIN,
    input logic clk
);

    // No reset in RTL; assertions are sampled on an external clock.

    // The concatenated outputs equal the 5-bit sum of A, B, and CIN.
    check_full_sum_function: assert property (
        @(posedge clk) {COUT, SUM} == ({1'b0, A} + {1'b0, B} + {4'b0, CIN})
    );

    // COUT is asserted exactly when the addition overflows 4 bits.
    check_cout_matches_overflow: assert property (
        @(posedge clk) COUT == (({1'b0, A} + {1'b0, B} + {4'b0, CIN}) >= 5'd16)
    );

    // With B and CIN low, the adder passes A through with no carry.
    check_a_passthrough_zero_addend: assert property (
        @(posedge clk) (B == 4'h0 && CIN == 1'b0) |-> (SUM == A && COUT == 1'b0)
    );

    // With A and CIN low, the adder passes B through with no carry.
    check_b_passthrough_zero_addend: assert property (
        @(posedge clk) (A == 4'h0 && CIN == 1'b0) |-> (SUM == B && COUT == 1'b0)
    );

    // All-zero inputs produce an all-zero result.
    check_zero_inputs_zero_outputs: assert property (
        @(posedge clk) (A == 4'h0 && B == 4'h0 && CIN == 1'b0) |-> (SUM == 4'h0 && COUT == 1'b0)
    );

    // A carry-in alone increments zero to one without overflow.
    check_cin_only_case: assert property (
        @(posedge clk) (A == 4'h0 && B == 4'h0 && CIN == 1'b1) |-> (SUM == 4'h1 && COUT == 1'b0)
    );

    // The maximum input combination produces 5'h1f.
    check_maximum_input_case: assert property (
        @(posedge clk) (A == 4'hf && B == 4'hf && CIN == 1'b1) |-> (SUM == 4'hf && COUT == 1'b1)
    );

endmodule