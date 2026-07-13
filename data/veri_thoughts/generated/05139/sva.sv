module gray_converter_sva (
    input logic        clk,
    input logic [3:0]  bin_in,
    input logic [3:0]  gray_out
);

    // Gray MSB matches binary MSB.
    check_gray_bit3_passthrough: assert property (
        @(posedge clk) gray_out[3] === bin_in[3]
    );

    // Gray bit 2 is bin_in[3] XOR bin_in[2].
    check_gray_bit2_xor: assert property (
        @(posedge clk) gray_out[2] === (bin_in[3] ^ bin_in[2])
    );

    // Gray bit 1 is bin_in[2] XOR bin_in[1].
    check_gray_bit1_xor: assert property (
        @(posedge clk) gray_out[1] === (bin_in[2] ^ bin_in[1])
    );

    // Gray bit 0 is bin_in[1] XOR bin_in[0].
    check_gray_bit0_xor: assert property (
        @(posedge clk) gray_out[0] === (bin_in[1] ^ bin_in[0])
    );

endmodule