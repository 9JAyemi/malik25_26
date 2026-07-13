module bin2gray_sva (
    input logic       clk,
    input logic [2:0] bin_in,
    input logic [2:0] gray_out
);

    // gray_out[2] passes through the binary MSB.
    check_gray_msb_passthrough: assert property (
        @(posedge clk) gray_out[2] == bin_in[2]
    );

    // gray_out[1] is the XOR of bin_in[2] and bin_in[1].
    check_gray_bit1_xor: assert property (
        @(posedge clk) gray_out[1] == (bin_in[2] ^ bin_in[1])
    );

    // gray_out[0] is the XOR of bin_in[1] and bin_in[0].
    check_gray_bit0_xor: assert property (
        @(posedge clk) gray_out[0] == (bin_in[1] ^ bin_in[0])
    );

    // The full output matches the implemented binary-to-Gray conversion.
    check_gray_vector_conversion: assert property (
        @(posedge clk) gray_out == {bin_in[2], (bin_in[2] ^ bin_in[1]), (bin_in[1] ^ bin_in[0])}
    );

    // The Gray output reconstructs the original binary input.
    check_gray_inverse_reconstruction: assert property (
        @(posedge clk) bin_in == {gray_out[2], (gray_out[2] ^ gray_out[1]), (gray_out[2] ^ gray_out[1] ^ gray_out[0])}
    );

endmodule