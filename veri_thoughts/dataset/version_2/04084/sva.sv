module ripple_carry_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic overflow
);

    // Combinational DUT with no explicit clock or reset; assertions sample on $global_clock.
    // A and B are 4-bit operands; S is the low 4 bits of A+B and overflow is the carry-out.

    // Combined outputs must equal the 5-bit addition result.
    check_full_addition_result: assert property (
        @($global_clock) ({overflow, S} == ({1'b0, A} + {1'b0, B}))
    );

    // Zero on A must pass B through with no carry.
    check_zero_a_passthrough: assert property (
        @($global_clock) (A == 4'h0) |-> ({overflow, S} == {1'b0, B})
    );

    // Zero on B must pass A through with no carry.
    check_zero_b_passthrough: assert property (
        @($global_clock) (B == 4'h0) |-> ({overflow, S} == {1'b0, A})
    );

    // The maximum input pair must produce 0x1E.
    check_max_plus_max: assert property (
        @($global_clock) ((A == 4'hF) && (B == 4'hF)) |-> ((S == 4'hE) && (overflow == 1'b1))
    );

    // Adding 1 to 0xF must wrap the sum and raise carry-out.
    check_f_plus_one_boundary: assert property (
        @($global_clock) ((A == 4'hF) && (B == 4'h1)) |-> ((S == 4'h0) && (overflow == 1'b1))
    );

    // Adding 0x8 and 0x8 must produce a carry-out with zero low bits.
    check_eight_plus_eight_boundary: assert property (
        @($global_clock) ((A == 4'h8) && (B == 4'h8)) |-> ((S == 4'h0) && (overflow == 1'b1))
    );

    // Sums that fit in 4 bits must not assert overflow.
    check_no_overflow_for_in_range_sum: assert property (
        @($global_clock) (({1'b0, A} + {1'b0, B}) <= 5'd15) |-> (overflow == 1'b0)
    );

    // Sums above 4-bit range must assert overflow.
    check_overflow_for_out_of_range_sum: assert property (
        @($global_clock) (({1'b0, A} + {1'b0, B}) >= 5'd16) |-> (overflow == 1'b1)
    );

endmodule