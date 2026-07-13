module binary_to_gray_sva (
    input logic       clk,
    input logic [7:0] bin_in,
    input logic [7:0] gray_out
);

    // gray_out must match the implemented XOR/shift equation.
    check_gray_equation: assert property (
        @(posedge clk) gray_out == (bin_in ^ {bin_in[7], bin_in[7:1]})
    );

    // The implemented MSB equation forces gray_out[7] low.
    check_gray_msb_zero: assert property (
        @(posedge clk) gray_out[7] == 1'b0
    );

    // The lower seven bits must match adjacent-bit XORs from bin_in.
    check_gray_lower_bits_equation: assert property (
        @(posedge clk) gray_out[6:0] == (bin_in[6:0] ^ bin_in[7:1])
    );

    // gray_out[6] is bin_in[6] XOR bin_in[7].
    check_gray_bit6_xor: assert property (
        @(posedge clk) gray_out[6] == (bin_in[6] ^ bin_in[7])
    );

    // gray_out[5] is bin_in[5] XOR bin_in[6].
    check_gray_bit5_xor: assert property (
        @(posedge clk) gray_out[5] == (bin_in[5] ^ bin_in[6])
    );

    // gray_out[4] is bin_in[4] XOR bin_in[5].
    check_gray_bit4_xor: assert property (
        @(posedge clk) gray_out[4] == (bin_in[4] ^ bin_in[5])
    );

    // gray_out[3] is bin_in[3] XOR bin_in[4].
    check_gray_bit3_xor: assert property (
        @(posedge clk) gray_out[3] == (bin_in[3] ^ bin_in[4])
    );

    // gray_out[2] is bin_in[2] XOR bin_in[3].
    check_gray_bit2_xor: assert property (
        @(posedge clk) gray_out[2] == (bin_in[2] ^ bin_in[3])
    );

    // gray_out[1] is bin_in[1] XOR bin_in[2].
    check_gray_bit1_xor: assert property (
        @(posedge clk) gray_out[1] == (bin_in[1] ^ bin_in[2])
    );

    // gray_out[0] is bin_in[0] XOR bin_in[1].
    check_gray_bit0_xor: assert property (
        @(posedge clk) gray_out[0] == (bin_in[0] ^ bin_in[1])
    );

endmodule