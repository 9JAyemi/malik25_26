module add4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic C_out
);

    // Combined outputs must equal the 5-bit sum of A and B.
    check_full_sum: assert property (
        @($global_clock) {C_out, S} == ({1'b0, A} + {1'b0, B})
    );

    // A zero B input must pass A through with no carry.
    check_b_zero_passthrough: assert property (
        @($global_clock) (B == 4'h0) |-> ({C_out, S} == {1'b0, A})
    );

    // A zero A input must pass B through with no carry.
    check_a_zero_passthrough: assert property (
        @($global_clock) (A == 4'h0) |-> ({C_out, S} == {1'b0, B})
    );

    // Sums below 16 must not assert carry out.
    check_no_carry_below_16: assert property (
        @($global_clock) (({1'b0, A} + {1'b0, B}) < 5'h10) |-> (C_out == 1'b0)
    );

    // Sums of 16 or more must assert carry out.
    check_carry_at_or_above_16: assert property (
        @($global_clock) (({1'b0, A} + {1'b0, B}) >= 5'h10) |-> (C_out == 1'b1)
    );

    // The least significant sum bit must be A[0] xor B[0].
    check_lsb_sum: assert property (
        @($global_clock) S[0] == (A[0] ^ B[0])
    );

    // All-zero inputs must produce all-zero outputs.
    check_zero_plus_zero: assert property (
        @($global_clock) ((A == 4'h0) && (B == 4'h0)) |-> ((S == 4'h0) && (C_out == 1'b0))
    );

    // Maximum inputs must produce 0x1E.
    check_max_plus_max: assert property (
        @($global_clock) ((A == 4'hF) && (B == 4'hF)) |-> ((S == 4'hE) && (C_out == 1'b1))
    );

endmodule