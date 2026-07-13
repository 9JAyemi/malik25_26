module top_module_sva (
    input logic a,
    input logic b,
    input logic [2:0] a_bitwise,
    input logic [2:0] b_bitwise,
    input logic [2:0] out_sum
);

    // Top-level output matches the implemented combinational function.
    check_out_sum_function: assert property (
        @($global_clock) out_sum == ((a ^ b) + (a_bitwise | b_bitwise))
    );

    // When the half-adder sum is 0, the output passes through the bitwise OR.
    check_xor_zero_passthrough: assert property (
        @($global_clock) (!(a ^ b)) |-> (out_sum == (a_bitwise | b_bitwise))
    );

    // When the half-adder sum is 1, the output is the bitwise OR plus one.
    check_xor_one_increment: assert property (
        @($global_clock) (a ^ b) |-> (out_sum == ((a_bitwise | b_bitwise) + 3'b001))
    );

    // Bit 0 reflects addition of the XOR result into bit 0 of the OR vector.
    check_out_sum_bit0: assert property (
        @($global_clock) out_sum[0] == ((a ^ b) ^ (a_bitwise[0] | b_bitwise[0]))
    );

    // Bit 1 reflects bit 1 of the OR vector plus carry from bit 0.
    check_out_sum_bit1: assert property (
        @($global_clock) out_sum[1] == ((a_bitwise[1] | b_bitwise[1]) ^ ((a ^ b) & (a_bitwise[0] | b_bitwise[0])))
    );

    // Bit 2 reflects bit 2 of the OR vector plus carry propagated through bit 1.
    check_out_sum_bit2: assert property (
        @($global_clock) out_sum[2] == ((a_bitwise[2] | b_bitwise[2]) ^ ((a ^ b) & (a_bitwise[0] | b_bitwise[0]) & (a_bitwise[1] | b_bitwise[1])))
    );

    // With zero 3-bit inputs, the output is just the zero-extended XOR of a and b.
    check_zero_vector_case: assert property (
        @($global_clock) ((a_bitwise == 3'b000) && (b_bitwise == 3'b000)) |-> (out_sum == {2'b00, (a ^ b)})
    );

    // Adding one to 3'b111 wraps in the 3-bit output, as implemented by the RTL width.
    check_full_scale_wraparound: assert property (
        @($global_clock) ((a ^ b) && ((a_bitwise | b_bitwise) == 3'b111)) |-> (out_sum == 3'b000)
    );

endmodule