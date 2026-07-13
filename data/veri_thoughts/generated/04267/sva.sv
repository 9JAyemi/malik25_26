module xor_concat_adder_sva (
    input logic        clk,
    input logic [7:0]  in_hi,
    input logic [7:0]  in_lo,
    input logic [15:0] final_output
);

    // Entire output matches the RTL expression after width extension.
    check_final_output_function: assert property (
        @(posedge clk)
        final_output == {7'b0, (in_hi[0] ^ in_lo[0]), in_hi}
    );

    // The low byte is the high input byte.
    check_low_byte_from_in_hi: assert property (
        @(posedge clk)
        final_output[7:0] == in_hi
    );

    // Bit 8 is the XOR of the two input LSBs.
    check_bit8_is_lsb_xor: assert property (
        @(posedge clk)
        final_output[8] == (in_hi[0] ^ in_lo[0])
    );

    // The upper seven bits are zero.
    check_upper_bits_zero: assert property (
        @(posedge clk)
        final_output[15:9] == 7'b0
    );

    // The upper byte is seven zeros with the XOR bit in bit 8.
    check_upper_byte_shape: assert property (
        @(posedge clk)
        final_output[15:8] == {7'b0, (in_hi[0] ^ in_lo[0])}
    );

endmodule