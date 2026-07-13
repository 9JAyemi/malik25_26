module decoder_3to8_sva (
    input logic       clk,
    input logic [2:0] in,
    input logic [7:0] out
);

    // out[0] is asserted only for input 3'b000.
    check_out0_decode: assert property (
        @(posedge clk) out[0] == (~in[2] & ~in[1] & ~in[0])
    );

    // out[1] is asserted only for input 3'b001.
    check_out1_decode: assert property (
        @(posedge clk) out[1] == (~in[2] & ~in[1] &  in[0])
    );

    // out[2] is asserted only for input 3'b010.
    check_out2_decode: assert property (
        @(posedge clk) out[2] == (~in[2] &  in[1] & ~in[0])
    );

    // out[3] is asserted only for input 3'b011.
    check_out3_decode: assert property (
        @(posedge clk) out[3] == (~in[2] &  in[1] &  in[0])
    );

    // out[4] is asserted only for input 3'b100.
    check_out4_decode: assert property (
        @(posedge clk) out[4] == ( in[2] & ~in[1] & ~in[0])
    );

    // out[5] is asserted only for input 3'b101.
    check_out5_decode: assert property (
        @(posedge clk) out[5] == ( in[2] & ~in[1] &  in[0])
    );

    // out[6] is asserted only for input 3'b110.
    check_out6_decode: assert property (
        @(posedge clk) out[6] == ( in[2] &  in[1] & ~in[0])
    );

    // out[7] is asserted only for input 3'b111.
    check_out7_decode: assert property (
        @(posedge clk) out[7] == ( in[2] &  in[1] &  in[0])
    );

    // The decoder output is always exactly one-hot.
    check_output_onehot: assert property (
        @(posedge clk) $onehot(out)
    );

    // The full output vector matches a left-shifted one-hot decode of input.
    check_full_vector_decode: assert property (
        @(posedge clk) out == (8'b0000_0001 << in)
    );

endmodule