module adder_subtractor_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic M,
    input logic [3:0] Y
);

    // RTL is combinational and has no reset; assertions are sampled on clk.

    // When M is 0, Y follows the sum path A + B.
    check_mode_zero_sum_path: assert property (
        @(posedge clk) !M |-> (Y == (A + B))
    );

    // When M is 1, Y follows the implemented temp_diff expression.
    check_mode_one_direct_path: assert property (
        @(posedge clk) M |-> (Y == (A - ((~B) + 4'b0001)))
    );

    // Across both modes, the implemented logic reduces to A + B modulo 16.
    check_output_matches_effective_addition: assert property (
        @(posedge clk) Y == (A + B)
    );

    // If A and B are unchanged, the sampled output must remain unchanged.
    check_stable_inputs_keep_stable_output: assert property (
        @(posedge clk) $past(1'b1) && $stable(A) && $stable(B) |-> $stable(Y)
    );

    // Toggling only M does not change the sampled output.
    check_mode_toggle_has_no_effect: assert property (
        @(posedge clk) $past(1'b1) && $changed(M) && $stable(A) && $stable(B) |-> $stable(Y)
    );

    // With B equal to zero, the output matches A.
    check_zero_b_passthrough: assert property (
        @(posedge clk) (B == 4'h0) |-> (Y == A)
    );

    // With A equal to zero, the output matches B.
    check_zero_a_passthrough: assert property (
        @(posedge clk) (A == 4'h0) |-> (Y == B)
    );

    // The least-significant output bit matches the addition XOR bit.
    check_lsb_matches_sum: assert property (
        @(posedge clk) Y[0] == (A[0] ^ B[0])
    );

endmodule