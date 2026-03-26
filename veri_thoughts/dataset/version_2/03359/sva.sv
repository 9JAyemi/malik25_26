module decoder_3to8_sva (
    input logic [2:0] in,
    input logic       ena,
    input logic [7:0] out
);

    // Output is all zeros when the decoder is disabled.
    check_disabled_clears_out: assert property (
        @($global_clock) (ena == 1'b0) |-> (out == 8'b00000000)
    );

    // Input 000 decodes to bit 0 when enabled.
    check_decode_000: assert property (
        @($global_clock) ((ena == 1'b1) && (in == 3'b000)) |-> (out == 8'b00000001)
    );

    // Input 001 decodes to bit 1 when enabled.
    check_decode_001: assert property (
        @($global_clock) ((ena == 1'b1) && (in == 3'b001)) |-> (out == 8'b00000010)
    );

    // Input 010 decodes to bit 2 when enabled.
    check_decode_010: assert property (
        @($global_clock) ((ena == 1'b1) && (in == 3'b010)) |-> (out == 8'b00000100)
    );

    // Input 011 decodes to bit 3 when enabled.
    check_decode_011: assert property (
        @($global_clock) ((ena == 1'b1) && (in == 3'b011)) |-> (out == 8'b00001000)
    );

    // Input 100 decodes to bit 4 when enabled.
    check_decode_100: assert property (
        @($global_clock) ((ena == 1'b1) && (in == 3'b100)) |-> (out == 8'b00010000)
    );

    // Input 101 decodes to bit 5 when enabled.
    check_decode_101: assert property (
        @($global_clock) ((ena == 1'b1) && (in == 3'b101)) |-> (out == 8'b00100000)
    );

    // Input 110 decodes to bit 6 when enabled.
    check_decode_110: assert property (
        @($global_clock) ((ena == 1'b1) && (in == 3'b110)) |-> (out == 8'b01000000)
    );

    // Input 111 decodes to bit 7 when enabled.
    check_decode_111: assert property (
        @($global_clock) ((ena == 1'b1) && (in == 3'b111)) |-> (out == 8'b10000000)
    );

endmodule