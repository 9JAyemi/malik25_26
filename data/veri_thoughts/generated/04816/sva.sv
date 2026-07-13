module adder_module_sva (
    input logic signed [31:0] A,
    input logic signed [31:0] B,
    input logic signed [31:0] Y
);

    // Y equals the signed sum of A and B.
    check_sum_matches_inputs: assert property (
        @($global_clock) Y == (A + B)
    );

    // If A is zero, Y equals B.
    check_zero_a_identity: assert property (
        @($global_clock) (A == 32'sd0) |-> (Y == B)
    );

    // If B is zero, Y equals A.
    check_zero_b_identity: assert property (
        @($global_clock) (B == 32'sd0) |-> (Y == A)
    );

    // If A is the additive inverse of B, Y is zero.
    check_additive_inverse_cancels: assert property (
        @($global_clock) (A == -B) |-> (Y == 32'sd0)
    );

endmodule