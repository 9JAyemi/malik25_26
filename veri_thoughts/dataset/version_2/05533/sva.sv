module decoder_3to8_sva (
    input logic clk,
    input logic [2:0] in,
    input logic [7:0] out
);

    // Output must equal the one-hot decode of the 3-bit input.
    check_decode_function: assert property (
        @(posedge clk) out == (8'b00000001 << in)
    );

    // Output must always contain exactly one asserted bit.
    check_output_onehot: assert property (
        @(posedge clk) $onehot(out)
    );

    // Input 000 must decode to bit 0.
    check_decode_000: assert property (
        @(posedge clk) (in == 3'b000) |-> (out == 8'b00000001)
    );

    // Input 001 must decode to bit 1.
    check_decode_001: assert property (
        @(posedge clk) (in == 3'b001) |-> (out == 8'b00000010)
    );

    // Input 010 must decode to bit 2.
    check_decode_010: assert property (
        @(posedge clk) (in == 3'b010) |-> (out == 8'b00000100)
    );

    // Input 011 must decode to bit 3.
    check_decode_011: assert property (
        @(posedge clk) (in == 3'b011) |-> (out == 8'b00001000)
    );

    // Input 100 must decode to bit 4.
    check_decode_100: assert property (
        @(posedge clk) (in == 3'b100) |-> (out == 8'b00010000)
    );

    // Input 101 must decode to bit 5.
    check_decode_101: assert property (
        @(posedge clk) (in == 3'b101) |-> (out == 8'b00100000)
    );

    // Input 110 must decode to bit 6.
    check_decode_110: assert property (
        @(posedge clk) (in == 3'b110) |-> (out == 8'b01000000)
    );

    // Input 111 must decode to bit 7.
    check_decode_111: assert property (
        @(posedge clk) (in == 3'b111) |-> (out == 8'b10000000)
    );

endmodule