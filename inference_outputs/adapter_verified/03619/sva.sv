module binary_decoder_3to8_sva (
    input logic clk,
    input logic [2:0] in,
    input logic [7:0] out
);

// 000 decodes to bit 0.
    check_decode_000: assert property (
        @(posedge clk) (in == 3'b000) |-> (out == 8'b00000001)
    );

// 001 decodes to bit 1.
    check_decode_001: assert property (
        @(posedge clk) (in == 3'b001) |-> (out == 8'b00000010)
    );

// 010 decodes to bit 2.
    check_decode_010: assert property (
        @(posedge clk) (in == 3'b010) |-> (out == 8'b00000100)
    );

// 011 decodes to bit 3.
    check_decode_011: assert property (
        @(posedge clk) (in == 3'b011) |-> (out == 8'b00001000)
    );

// 100 decodes to bit 4.
    check_decode_100: assert property (
        @(posedge clk) (in == 3'b100) |-> (out == 8'b00010000)
    );

// 101 decodes to bit 5.
    check_decode_101: assert property (
        @(posedge clk) (in == 3'b101) |-> (out == 8'b00100000)
    );

// 110 decodes to bit 6.
    check_decode_110: assert property (
        @(posedge clk) (in == 3'b110) |-> (out == 8'b01000000)
    );

// 111 decodes to bit 7.
    check_decode_111: assert property (
        @(posedge clk) (in == 3'b111) |-> (out == 8'b10000000)
    );

// Any unknown input value drives zero.
    check_default_zero: assert property (
        @(posedge clk) (in != 3'b000 && in != 3'b001 && in != 3'b010 && in != 3'b011 &&
                        in != 3'b100 && in != 3'b101 && in != 3'b110 && in != 3'b111)
        |-> (out == 8'b00000000)
    );

// Output is always one-hot.
    check_onehot_output: assert property (
        @(posedge clk) $onehot(out)
    );

endmodule
