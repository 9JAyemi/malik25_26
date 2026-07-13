module simple_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C
);

    // C always equals the 4-bit sum of A and B.
    check_sum_matches_inputs: assert property (
        @($global_clock) C == (A + B)
    );

    // If both inputs stay the same, the output stays the same.
    check_output_stable_when_inputs_stable: assert property (
        @($global_clock) ($stable(A) && $stable(B)) |-> $stable(C)
    );

    // A zero B input passes A through to C.
    check_b_zero_identity: assert property (
        @($global_clock) (B == 4'h0) |-> (C == A)
    );

    // A zero A input passes B through to C.
    check_a_zero_identity: assert property (
        @($global_clock) (A == 4'h0) |-> (C == B)
    );

endmodule