module adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C,
    input logic CO
);

    // Combined carry and sum equal the 5-bit addition result.
    check_combined_sum_correct: assert property (
        @($global_clock) {CO, C} == ({1'b0, A} + {1'b0, B})
    );

    // The least-significant sum bit is the XOR of the input LSBs.
    check_lsb_sum_bit: assert property (
        @($global_clock) C[0] == (A[0] ^ B[0])
    );

    // A zero on A passes B through with no carry.
    check_a_zero_identity: assert property (
        @($global_clock) (A == 4'h0) |-> ({CO, C} == {1'b0, B})
    );

    // A zero on B passes A through with no carry.
    check_b_zero_identity: assert property (
        @($global_clock) (B == 4'h0) |-> ({CO, C} == {1'b0, A})
    );

    // No carry-out is possible when both input MSBs are clear.
    check_no_carry_when_top_bits_clear: assert property (
        @($global_clock) (!A[3] && !B[3]) |-> (CO == 1'b0)
    );

    // Carry-out is guaranteed when both input MSBs are set.
    check_carry_when_top_bits_set: assert property (
        @($global_clock) (A[3] && B[3]) |-> (CO == 1'b1)
    );

    // When carry-out is low, zero-extending C reproduces the full sum.
    check_no_carry_sum_encoding: assert property (
        @($global_clock) (CO == 1'b0) |-> ({1'b0, C} == ({1'b0, A} + {1'b0, B}))
    );

    // When carry-out is high, prefixing C with 1 reproduces the full sum.
    check_carry_sum_encoding: assert property (
        @($global_clock) (CO == 1'b1) |-> ({1'b1, C} == ({1'b0, A} + {1'b0, B}))
    );

endmodule