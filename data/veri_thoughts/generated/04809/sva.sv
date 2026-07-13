module decoder_sva (
    input logic clk,
    input logic [2:0] in,
    input logic [7:0] out
);

    // Input 000 decodes to bit 0.
    check_decode_000: assert property (
        @(posedge clk) (in == 3'b000) |-> (out == 8'b00000001)
    );

    // Input 001 decodes to bit 1.
    check_decode_001: assert property (
        @(posedge clk) (in == 3'b001) |-> (out == 8'b00000010)
    );

    // Input 010 decodes to bit 2.
    check_decode_010: assert property (
        @(posedge clk) (in == 3'b010) |-> (out == 8'b00000100)
    );

    // Input 011 decodes to bit 3.
    check_decode_011: assert property (
        @(posedge clk) (in == 3'b011) |-> (out == 8'b00001000)
    );

    // Input 100 decodes to bit 4.
    check_decode_100: assert property (
        @(posedge clk) (in == 3'b100) |-> (out == 8'b00010000)
    );

    // Input 101 decodes to bit 5.
    check_decode_101: assert property (
        @(posedge clk) (in == 3'b101) |-> (out == 8'b00100000)
    );

    // Input 110 decodes to bit 6.
    check_decode_110: assert property (
        @(posedge clk) (in == 3'b110) |-> (out == 8'b01000000)
    );

    // Input 111 decodes to bit 7.
    check_decode_111: assert property (
        @(posedge clk) (in == 3'b111) |-> (out == 8'b10000000)
    );

    // Output is always one-hot.
    check_output_onehot: assert property (
        @(posedge clk) $onehot(out)
    );

endmodule