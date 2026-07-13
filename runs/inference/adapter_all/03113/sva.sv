module addition_module_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [8:0] sum,
    input logic       carry
);

    // sum must equal the 9-bit addition of A and B.
    check_sum_matches_addition: assert property (
        @($global_clock) sum == ({1'b0, A} + {1'b0, B})
    );

    // carry must reflect the MSB of the 9-bit addition result.
    check_carry_matches_addition: assert property (
        @($global_clock) carry == (({1'b0, A} + {1'b0, B})[8])
    );

    // Adding zero on B must pass A through with no carry.
    check_add_zero_on_b: assert property (
        @($global_clock) (B == 8'h00) |-> (sum == {1'b0, A} && carry == 1'b0)
    );

    // Adding zero on A must pass B through with no carry.
    check_add_zero_on_a: assert property (
        @($global_clock) (A == 8'h00) |-> (sum == {1'b0, B} && carry == 1'b0)
    );

    // The least-significant sum bit is the XOR of the input LSBs.
    check_lsb_sum_xor: assert property (
        @($global_clock) sum[0] == (A[0] ^ B[0])
    );

    // Carry-out must be high when the 8-bit addition overflows.
    check_carry_on_overflow: assert property (
        @($global_clock) (({1'b0, A} + {1'b0, B}) > 9'h0FF) |-> (carry == 1'b1)
    );

    // Carry-out must be low when the 8-bit addition does not overflow.
    check_carry_without_overflow: assert property (
        @($global_clock) (({1'b0, A} + {1'b0, B}) <= 9'h0FF) |-> (carry == 1'b0)
    );

    // The full output must match the 9-bit addition result.
    check_full_output_matches_addition: assert property (
        @($global_clock) {carry, sum} == ({1'b0, A} + {1'b0, B})
    );

endmodule