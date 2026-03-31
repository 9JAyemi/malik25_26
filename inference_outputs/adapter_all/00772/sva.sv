module decoder_4to16_sva (
    input logic        clk,
    input logic [3:0]  in,
    input logic [15:0] out
);

    // Input 0 maps to bit 0.
    check_decode_0000: assert property (
        @(posedge clk) (in == 4'b0000) |-> (out == 16'h0001)
    );

    // Input 1 maps to bit 1.
    check_decode_0001: assert property (
        @(posedge clk) (in == 4'b0001) |-> (out == 16'h0002)
    );

    // Input 2 maps to bit 2.
    check_decode_0010: assert property (
        @(posedge clk) (in == 4'b0010) |-> (out == 16'h0004)
    );

    // Input 3 maps to bit 3.
    check_decode_0011: assert property (
        @(posedge clk) (in == 4'b0011) |-> (out == 16'h0008)
    );

    // Input 4 maps to bit 4.
    check_decode_0100: assert property (
        @(posedge clk) (in == 4'b0100) |-> (out == 16'h0010)
    );

    // Input 5 maps to bit 5.
    check_decode_0101: assert property (
        @(posedge clk) (in == 4'b0101) |-> (out == 16'h0020)
    );

    // Input 6 maps to bit 6.
    check_decode_0110: assert property (
        @(posedge clk) (in == 4'b0110) |-> (out == 16'h0040)
    );

    // Input 7 maps to bit 7.
    check_decode_0111: assert property (
        @(posedge clk) (in == 4'b0111) |-> (out == 16'h0080)
    );

    // Input 8 maps to bit 8.
    check_decode_1000: assert property (
        @(posedge clk) (in == 4'b1000) |-> (out == 16'h0100)
    );

    // Input 9 maps to bit 9.
    check_decode_1001: assert property (
        @(posedge clk) (in == 4'b1001) |-> (out == 16'h0200)
    );

    // Input 10 maps to bit 10.
    check_decode_1010: assert property (
        @(posedge clk) (in == 4'b1010) |-> (out == 16'h0400)
    );

    // Input 11 maps to bit 11.
    check_decode_1011: assert property (
        @(posedge clk) (in == 4'b1011) |-> (out == 16'h0800)
    );

    // Input 12 maps to bit 12.
    check_decode_1100: assert property (
        @(posedge clk) (in == 4'b1100) |-> (out == 16'h1000)
    );

    // Input 13 maps to bit 13.
    check_decode_1101: assert property (
        @(posedge clk) (in == 4'b1101) |-> (out == 16'h2000)
    );

    // Input 14 maps to bit 14.
    check_decode_1110: assert property (
        @(posedge clk) (in == 4'b1110) |-> (out == 16'h4000)
    );

    // Input 15 maps to bit 15.
    check_decode_1111: assert property (
        @(posedge clk) (in == 4'b1111) |-> (out == 16'h8000)
    );

    // Output is always exactly one bit set.
    check_output_onehot: assert property (
        @(posedge clk) $onehot(out)
    );

endmodule