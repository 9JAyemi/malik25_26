module binary_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       C_in,
    input logic [3:0] S
);

    // S always reflects the 4-bit sum of A, B, and C_in.
    check_output_matches_sum: assert property (
        @($global_clock) S == (A + B + C_in)
    );

    // With B and C_in low, S passes A unchanged.
    check_a_passthrough_when_b_and_cin_zero: assert property (
        @($global_clock) (B == 4'b0000 && C_in == 1'b0) |-> (S == A)
    );

    // With A and C_in low, S passes B unchanged.
    check_b_passthrough_when_a_and_cin_zero: assert property (
        @($global_clock) (A == 4'b0000 && C_in == 1'b0) |-> (S == B)
    );

    // With both operands low, S equals the zero-extended carry-in.
    check_cin_only_result: assert property (
        @($global_clock) (A == 4'b0000 && B == 4'b0000) |-> (S == {3'b000, C_in})
    );

    // The least-significant sum bit follows full-adder parity.
    check_lsb_full_adder_behavior: assert property (
        @($global_clock) S[0] == (A[0] ^ B[0] ^ C_in)
    );

endmodule