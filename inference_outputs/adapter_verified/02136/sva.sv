module binary_to_gray_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [3:0] out
);

// out[0] is a direct copy of in[0].
    check_out0_is_in0: assert property (
        @(posedge clk) out[0] == in[0]
    );

// out[1] is in[0] XOR in[1].
    check_out1_is_in0_xor_in1: assert property (
        @(posedge clk) out[1] == (in[0] ^ in[1])
    );

// out[2] is in[1] XOR in[2] XOR in[0].
    check_out2_is_in1_xor_in2_xor_in0: assert property (
        @(posedge clk) out[2] == (in[1] ^ in[2] ^ in[0])
    );

// out[3] is in[2] XOR in[3] XOR in[1].
    check_out3_is_in2_xor_in3_xor_in1: assert property (
        @(posedge clk) out[3] == (in[2] ^ in[3] ^ in[1])
    );

endmodule
