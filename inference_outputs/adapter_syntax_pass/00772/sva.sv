module decoder_4to16_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [15:0] out
);

    // Output is always one-hot.
    check_out_onehot: assert property (
        @(posedge clk) $onehot(out)
    );

    // Input 0000 decodes to bit 0.
    check_decode_0000: assert property (
        @(posedge clk) (in == 4'h0) |-> (out == 16'h0001)
    );

    // Input 0001 decodes to bit 1.
    check_decode_0001: assert property (
        @(posedge clk) (in == 4'h1) |-> (out == 16'h0002)
    );

    // Input 0010 decodes to bit 2.
    check_decode_0010: assert property (
        @(posedge clk) (in == 4'h2) |-> (out == 16'h0004)
    );

    // Input 0011 decodes to bit 3.
    check_decode_0011: assert property (
        @(posedge clk) (in == 4'h3) |-> (out == 16'h0008)
    );

    // Input 0100 decodes to bit 4.
    check_decode_0100: assert property (
        @(posedge clk) (in == 4'h4) |-> (out == 16'h0010)
    );

    // Input 0101 decodes to bit 5.
    check_decode_0101: assert property (
        @(posedge clk) (in == 4'h5) |-> (out == 16'h0020)
    );

    // Input 0110 decodes to bit 6.
    check_decode_0110: assert property (
        @(posedge clk) (in == 4'h6) |-> (out == 16'h0040)
    );

    // Input 0111 decodes to bit 7.
    check_decode_0111: assert property (
        @(posedge clk) (in == 4'h7) |-> (out == 16'h0080)
    );

    // Input 1000 decodes to bit 8.
    check_decode_1000: assert property (
        @(posedge clk) (in == 4'h8) |-> (out == 16'h0100)
    );

    // Input 1001 decodes to bit 9.
    check_decode_1001: assert property (
        @(posedge clk) (in == 4'h9) |-> (out == 16'h0200)
    );

    // Input 1010 decodes to bit 10.
    check_decode_1010: assert property (
        @(posedge clk) (in == 4'hA) |-> (out == 16'h0400)
    );

    // Input 1011 decodes to bit 11.
    check_decode_1011: assert property (
        @(posedge clk) (in == 4'hB) |-> (out == 16'h0800)
    );

    // Input 1100 decodes to bit 12.
    check_decode_1100: assert property (
        @(posedge clk) (in == 4'hC) |-> (out == 16'h1000)
    );

    // Input 1101 decodes to bit 13.
    check_decode_1101: assert property (
        @(posedge clk) (in == 4'hD) |-> (out == 16'h2000)
    );

    // Input 1110 decodes to bit 14.
    check_decode_1110: assert property (
        @(posedge clk) (in == 4'hE) |-> (out == 16'h4000)
    );

    // Input 1111 decodes to bit 15.
    check_decode_1111: assert property (
        @(posedge clk) (in == 4'hF) |-> (out == 16'h8000)
    );

endmodule