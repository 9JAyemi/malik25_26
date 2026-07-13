module addition_module_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [8:0] sum,
    input logic carry
);

    // sum must equal the 8-bit addition of A and B.
    check_sum_matches_addition: assert property (
        @($global_clock) sum == {1'b0, A} + {1'b0, B}
    );

    // carry must be high exactly when the 8-bit addition overflows.
    check_carry_matches_overflow: assert property (
        @($global_clock) carry == (({1'b0, A} + {1'b0, B}) > 8'hFF)
    );

    // carry must match the MSB of the concatenated sum.
    check_carry_matches_sum_msb: assert property (
        @($global_clock) carry == sum[8]
    );

    // The least-significant sum bit must be the XOR of the input LSBs.
    check_lsb_sum_is_xor: assert property (
        @($global_clock) sum[0] == (A[0] ^ B[0])
    );

    // Adding zero on A must pass B through with no carry.
    check_zero_a_passthrough: assert property (
        @($global_clock) (A == 8'h00) |-> ((sum == {1'b0, B}) && (carry == 1'b0))
    );

    // Adding zero on B must pass A through with no carry.
    check_zero_b_passthrough: assert property (
        @($global_clock) (B == 8'h00) |-> ((sum == {1'b0, A}) && (carry == 1'b0))
    );

    // The maximum input pair must produce 8'hFF with carry asserted.
    check_max_input_case: assert property (
        @($global_clock) ((A == 8'hFF) && (B == 8'hFF)) |-> ((sum == 9'h1FE) && (carry == 1'b1))
    );

endmodule