module binary_to_gray_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [3:0] out
);

    // out[0] is a direct copy of in[0].
    check_out0_passthrough: assert property (
        @(posedge clk) out[0] == in[0]
    );

    // out[1] is the XOR of in[0] and in[1].
    check_out1_xor: assert property (
        @(posedge clk) out[1] == (in[0] ^ in[1])
    );

    // out[2] is the XOR of in[1], in[2], and in[0].
    check_out2_xor: assert property (
        @(posedge clk) out[2] == (in[1] ^ in[2] ^ in[0])
    );

    // out[3] is the XOR of in[2], in[3], and in[1].
    check_out3_xor: assert property (
        @(posedge clk) out[3] == (in[2] ^ in[3] ^ in[1])
    );

endmodule