module binary_decoder_3to8_sva (
    input logic clk,
    input logic [2:0] in,
    input logic [7:0] out
);

    // Output is never multi-hot.
    check_out_onehot0: assert property (
        @(posedge clk) disable iff (1'b0) $onehot0(out)
    );

    // Input 000 selects bit 0.
    check_decode_000: assert property (
        @(posedge clk) disable iff (1'b0) (in == 3'b000) |-> (out == 8'b00000001)
    );

    // Input 001 selects bit 1.
    check_decode_001: assert property (
        @(posedge clk) disable iff (1'b0) (in == 3'b001) |-> (out == 8'b00000010)
    );

    // Input 010 selects bit 2.
    check_decode_010: assert property (
        @(posedge clk) disable iff (1'b0) (in == 3'b010) |-> (out == 8'b00000100)
    );

    // Input 011 selects bit 3.
    check_decode_011: assert property (
        @(posedge clk) disable iff (1'b0) (in == 3'b011) |-> (out == 8'b00001000)
    );

    // Input 100 selects bit 4.
    check_decode_100: assert property (
        @(posedge clk) disable iff (1'b0) (in == 3'b100) |-> (out == 8'b00010000)
    );

    // Input 101 selects bit 5.
    check_decode_101: assert property (
        @(posedge clk) disable iff (1'b0) (in == 3'b101) |-> (out == 8'b00100000)
    );

    // Input 110 selects bit 6.
    check_decode_110: assert property (
        @(posedge clk) disable iff (1'b0) (in == 3'b110) |-> (out == 8'b01000000)
    );

    // Input 111 selects bit 7.
    check_decode_111: assert property (
        @(posedge clk) disable iff (1'b0) (in == 3'b111) |-> (out == 8'b10000000)
    );

    // Unknown input values drive the default zero output.
    check_decode_unknown_default_zero: assert property (
        @(posedge clk) disable iff (1'b0) $isunknown(in) |-> (out == 8'b00000000)
    );

endmodule