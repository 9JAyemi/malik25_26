module decoder_4_to_16_sva (
    input logic clk,
    input logic [1:0] AB,
    input logic [15:0] Y
);

    // AB=00 drives only bit 0 high.
    check_decode_00: assert property (
        @(posedge clk) (AB == 2'b00) |-> (Y == 16'b0000000000000001)
    );

    // AB=01 drives only bit 1 high.
    check_decode_01: assert property (
        @(posedge clk) (AB == 2'b01) |-> (Y == 16'b0000000000000010)
    );

    // AB=10 drives only bit 2 high.
    check_decode_10: assert property (
        @(posedge clk) (AB == 2'b10) |-> (Y == 16'b0000000000000100)
    );

    // AB=11 drives only bit 3 high.
    check_decode_11: assert property (
        @(posedge clk) (AB == 2'b11) |-> (Y == 16'b0000000000001000)
    );

    // Unused upper outputs are always low.
    check_upper_bits_zero: assert property (
        @(posedge clk) Y[15:4] == 12'b000000000000
    );

    // Exactly one lower output bit is asserted.
    check_lower_nibble_onehot: assert property (
        @(posedge clk) $onehot(Y[3:0])
    );

endmodule