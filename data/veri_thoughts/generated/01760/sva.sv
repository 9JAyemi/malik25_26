module binary_to_gray_sva (
    input logic clk,
    input logic [3:0] bin_in,
    input logic [3:0] gray_out
);
    // Gray MSB equals binary MSB.
    check_gray_msb_passthrough: assert property (
        @(posedge clk) gray_out[3] == bin_in[3]
    );

    // Gray[2] equals bin_in[3] XOR bin_in[2].
    check_gray_bit2_is_b3_xor_b2: assert property (
        @(posedge clk) gray_out[2] == (bin_in[3] ^ bin_in[2])
    );

    // Gray[1] equals bin_in[2] XOR bin_in[1].
    check_gray_bit1_is_b2_xor_b1: assert property (
        @(posedge clk) gray_out[1] == (bin_in[2] ^ bin_in[1])
    );

    // Gray[0] equals bin_in[1] XOR bin_in[0].
    check_gray_bit0_is_b1_xor_b0: assert property (
        @(posedge clk) gray_out[0] == (bin_in[1] ^ bin_in[0])
    );

    // Vector mapping equals {b3, b3^b2, b2^b1, b1^b0}.
    check_gray_vector_mapping: assert property (
        @(posedge clk) gray_out == {bin_in[3], (bin_in[3] ^ bin_in[2]), (bin_in[2] ^ bin_in[1]), (bin_in[1] ^ bin_in[0])}
    );

    // Binary[3] recovered from Gray equals gray_out[3].
    check_bin3_from_gray: assert property (
        @(posedge clk) bin_in[3] == gray_out[3]
    );

    // Binary[2] recovered as gray_out[3] XOR gray_out[2].
    check_bin2_from_gray: assert property (
        @(posedge clk) bin_in[2] == (gray_out[3] ^ gray_out[2])
    );

    // Binary[1] recovered as gray_out[3] XOR gray_out[2] XOR gray_out[1].
    check_bin1_from_gray: assert property (
        @(posedge clk) bin_in[1] == (gray_out[3] ^ gray_out[2] ^ gray_out[1])
    );

    // Binary[0] recovered as gray_out[3] XOR gray_out[2] XOR gray_out[1] XOR gray_out[0].
    check_bin0_from_gray: assert property (
        @(posedge clk) bin_in[0] == (gray_out[3] ^ gray_out[2] ^ gray_out[1] ^ gray_out[0])
    );
endmodule