module decoder_4to16_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [15:0] out
);

// Output is always exactly one-hot.
    check_out_onehot: assert property (
        @(posedge clk) $onehot(out)
    );

// Input 0000 decodes to bit 0.
    check_decode_0000: assert property (
        @(posedge clk) (in == 4'b0000) |-> (out == 16'b0000000000000001)
    );

// Input 0001 decodes to bit 1.
    check_decode_0001: assert property (
        @(posedge clk) (in == 4'b0001) |-> (out == 16'b0000000000000010)
    );

// Input 0010 decodes to bit 2.
    check_decode_0010: assert property (
        @(posedge clk) (in == 4'b0010) |-> (out == 16'b0000000000000100)
    );

// Input 0011 decodes to bit 3.
    check_decode_0011: assert property (
        @(posedge clk) (in == 4'b0011) |-> (out == 16'b0000000000001000)
    );

// Input 0100 decodes to bit 4.
    check_decode_0100: assert property (
        @(posedge clk) (in == 4'b0100) |-> (out == 16'b0000000000010000)
    );

// Input 0101 decodes to bit 5.
    check_decode_0101: assert property (
        @(posedge clk) (in == 4'b0101) |-> (out == 16'b0000000000100000)
    );

// Input 0110 decodes to bit 6.
    check_decode_0110: assert property (
        @(posedge clk) (in == 4'b0110) |-> (out == 16'b0000000001000000)
    );

// Input 0111 decodes to bit 7.
    check_decode_0111: assert property (
        @(posedge clk) (in == 4'b0111) |-> (out == 16'b0000000010000000)
    );

// Input 1000 decodes to bit 8.
    check_decode_1000: assert property (
        @(posedge clk) (in == 4'b1000) |-> (out == 16'b0000000100000000)
    );

// Input 1001 decodes to bit 9.
    check_decode_1001: assert property (
        @(posedge clk) (in == 4'b1001) |-> (out == 16'b0000001000000000)
    );

// Input 1010 decodes to bit 10.
    check_decode_1010: assert property (
        @(posedge clk) (in == 4'b1010) |-> (out == 16'b0000010000000000)
    );

// Input 1011 decodes to bit 11.
    check_decode_1011: assert property (
        @(posedge clk) (in == 4'b1011) |-> (out == 16'b0000100000000000)
    );

// Input 1100 decodes to bit 12.
    check_decode_1100: assert property (
        @(posedge clk) (in == 4'b1100) |-> (out == 16'b0001000000000000)
    );

// Input 1101 decodes to bit 13.
    check_decode_1101: assert property (
        @(posedge clk) (in == 4'b1101) |-> (out == 16'b0010000000000000)
    );

// Input 1110 decodes to bit 14.
    check_decode_1110: assert property (
        @(posedge clk) (in == 4'b1110) |-> (out == 16'b0100000000000000)
    );

// Input 1111 decodes to bit 15.
    check_decode_1111: assert property (
        @(posedge clk) (in == 4'b1111) |-> (out == 16'b1000000000000000)
    );

endmodule
