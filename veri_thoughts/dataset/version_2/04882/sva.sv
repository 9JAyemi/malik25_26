module adder_sva (
    input logic [2:0] A,
    input logic [2:0] B,
    input logic [2:0] S,
    input logic Cout
);

    // No RTL clock or reset is present; sample the combinational logic on $global_clock.

    // Full output must equal the zero-extended sum of A and B.
    check_full_sum: assert property (
        @($global_clock) {Cout, S} == ({1'b0, A} + {1'b0, B})
    );

    // Adding zero on B must pass A through with no carry.
    check_b_zero_passthrough: assert property (
        @($global_clock) (B == 3'b000) |-> ({Cout, S} == {1'b0, A})
    );

    // Adding zero on A must pass B through with no carry.
    check_a_zero_passthrough: assert property (
        @($global_clock) (A == 3'b000) |-> ({Cout, S} == {1'b0, B})
    );

    // Sums below 8 must not assert carry-out.
    check_no_carry_below_eight: assert property (
        @($global_clock) (({1'b0, A} + {1'b0, B}) < 4'd8) |-> (Cout == 1'b0)
    );

    // Sums of 8 or more must assert carry-out.
    check_carry_at_or_above_eight: assert property (
        @($global_clock) (({1'b0, A} + {1'b0, B}) >= 4'd8) |-> (Cout == 1'b1)
    );

    // The maximum input pair must produce decimal 14.
    check_max_input_sum: assert property (
        @($global_clock) ((A == 3'b111) && (B == 3'b111)) |-> ({Cout, S} == 4'd14)
    );

endmodule