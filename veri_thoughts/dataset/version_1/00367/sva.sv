module binary_to_gray_sva(
    input logic       clk,
    input logic [3:0] bin_in,
    input logic [3:0] gray_out
);

    // gray_out[3] matches the binary MSB.
    check_gray_msb: assert property (
        @(posedge clk) gray_out[3] == bin_in[3]
    );

    // gray_out[2] is bin_in[2] XOR bin_in[3].
    check_gray_bit2: assert property (
        @(posedge clk) gray_out[2] == (bin_in[2] ^ bin_in[3])
    );

    // gray_out[1] is bin_in[1] XOR bin_in[2].
    check_gray_bit1: assert property (
        @(posedge clk) gray_out[1] == (bin_in[1] ^ bin_in[2])
    );

    // gray_out[0] is bin_in[0] XOR bin_in[1].
    check_gray_bit0: assert property (
        @(posedge clk) gray_out[0] == (bin_in[0] ^ bin_in[1])
    );

endmodule