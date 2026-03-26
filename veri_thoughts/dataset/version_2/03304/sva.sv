module adder4_sva(
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] O,
    input logic C
);

    // Combined carry and sum must equal the 5-bit addition of A and B.
    check_total_sum: assert property (
        @($global_clock) {C, O} == ({1'b0, A} + {1'b0, B})
    );

    // Carry-out must assert exactly when the 4-bit addition overflows.
    check_carry_bit: assert property (
        @($global_clock) C == (({1'b0, A} + {1'b0, B}) >= 5'd16)
    );

    // The first stage has Cin tied low, so O[0] is A[0] XOR B[0].
    check_lsb_stage: assert property (
        @($global_clock) O[0] == (A[0] ^ B[0])
    );

    // The second stage sum uses the carry from bit 0, which is A[0] & B[0].
    check_bit1_ripple: assert property (
        @($global_clock) O[1] == (A[1] ^ B[1] ^ (A[0] & B[0]))
    );

    // Adding zero on A passes B through with no carry.
    check_zero_a_passthrough: assert property (
        @($global_clock) (A == 4'b0000) |-> ({C, O} == {1'b0, B})
    );

    // Adding zero on B passes A through with no carry.
    check_zero_b_passthrough: assert property (
        @($global_clock) (B == 4'b0000) |-> ({C, O} == {1'b0, A})
    );

endmodule