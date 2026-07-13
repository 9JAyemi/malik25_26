module rca_top_sva (
    input logic [15:0] final_output,
    input logic        carry_output,
    input logic [15:0] input1,
    input logic [15:0] input2
);

    // Combined carry and sum match the 17-bit unsigned addition.
    check_full_sum: assert property (
        @($global_clock)
        ({carry_output, final_output} == ({1'b0, input1} + {1'b0, input2}))
    );

    // Sum output is the low 16 bits of the unsigned addition.
    check_sum_truncation: assert property (
        @($global_clock)
        (final_output == (input1 + input2))
    );

    // Carry output matches unsigned overflow relative to input1.
    check_carry_overflow_input1: assert property (
        @($global_clock)
        (carry_output == (final_output < input1))
    );

    // Carry output matches unsigned overflow relative to input2.
    check_carry_overflow_input2: assert property (
        @($global_clock)
        (carry_output == (final_output < input2))
    );

    // Bit 0 sum is XOR because the adder carry-in is tied low.
    check_lsb_sum_xor: assert property (
        @($global_clock)
        (final_output[0] == (input1[0] ^ input2[0]))
    );

    // Zero on input1 passes input2 through with no carry.
    check_zero_input1_passthrough: assert property (
        @($global_clock)
        ((input1 == 16'h0000) |-> ((final_output == input2) && (carry_output == 1'b0)))
    );

    // Zero on input2 passes input1 through with no carry.
    check_zero_input2_passthrough: assert property (
        @($global_clock)
        ((input2 == 16'h0000) |-> ((final_output == input1) && (carry_output == 1'b0)))
    );

    // If both MSBs are clear, the addition cannot overflow.
    check_no_overflow_when_msbs_clear: assert property (
        @($global_clock)
        (((input1[15] == 1'b0) && (input2[15] == 1'b0)) |-> (carry_output == 1'b0))
    );

endmodule