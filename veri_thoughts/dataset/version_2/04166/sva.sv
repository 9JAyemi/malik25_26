module simple_adder_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [4:0] sum
);

    // sum must equal the zero-extended addition of a and b.
    check_sum_matches_addition: assert property (
        @($global_clock) sum == ({1'b0, a} + {1'b0, b})
    );

    // The least significant sum bit must match bit-0 addition.
    check_sum_lsb_matches_xor: assert property (
        @($global_clock) sum[0] == (a[0] ^ b[0])
    );

    // The carry-out bit must match the addition overflow.
    check_sum_carry_out: assert property (
        @($global_clock) sum[4] == ({1'b0, a} + {1'b0, b})[4]
    );

    // Adding zero on a must pass b through.
    check_zero_a_passthrough: assert property (
        @($global_clock) (a == 4'b0000) |-> (sum == {1'b0, b})
    );

    // Adding zero on b must pass a through.
    check_zero_b_passthrough: assert property (
        @($global_clock) (b == 4'b0000) |-> (sum == {1'b0, a})
    );

    // The sum must be at least as large as a.
    check_sum_not_smaller_than_a: assert property (
        @($global_clock) sum >= {1'b0, a}
    );

    // The sum must be at least as large as b.
    check_sum_not_smaller_than_b: assert property (
        @($global_clock) sum >= {1'b0, b}
    );

    // Reversing operands must not change the computed sum.
    check_sum_commutative: assert property (
        @($global_clock) sum == ({1'b0, b} + {1'b0, a})
    );

endmodule