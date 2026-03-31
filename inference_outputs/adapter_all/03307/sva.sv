module adder_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] S,
    input logic       C_out
);

    // No RTL clock or reset; sample this combinational logic on the formal global clock.

    // The 9-bit output must equal the arithmetic sum of A and B.
    check_full_sum: assert property (
        @($global_clock) {C_out, S} == ({1'b0, A} + {1'b0, B})
    );

    // The 8-bit sum output must match the low 8 bits of the arithmetic sum.
    check_sum_low_bits: assert property (
        @($global_clock) S == (A + B)
    );

    // Carry-out must be low whenever the arithmetic sum fits in 8 bits.
    check_carry_low_when_no_overflow: assert property (
        @($global_clock) (({1'b0, A} + {1'b0, B}) <= 9'd255) |-> (C_out == 1'b0)
    );

    // Carry-out must be high whenever the arithmetic sum exceeds 8 bits.
    check_carry_high_when_overflow: assert property (
        @($global_clock) (({1'b0, A} + {1'b0, B}) > 9'd255) |-> (C_out == 1'b1)
    );

    // Adding zero on B must pass A through with no carry.
    check_add_zero_b: assert property (
        @($global_clock) (B == 8'h00) |-> (S == A && C_out == 1'b0)
    );

    // Adding zero on A must pass B through with no carry.
    check_add_zero_a: assert property (
        @($global_clock) (A == 8'h00) |-> (S == B && C_out == 1'b0)
    );

    // The maximum input pair must produce 0xFF with carry-out set.
    check_max_plus_max: assert property (
        @($global_clock) (A == 8'hFF && B == 8'hFF) |-> (S == 8'hFF && C_out == 1'b1)
    );

endmodule