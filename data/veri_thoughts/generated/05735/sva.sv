module decoder_3to8_sva (
    input logic clk,
    input logic [2:0] in,
    input logic [7:0] out
);

    // 000 selects bit 0.
    check_decode_000: assert property (
        @(posedge clk) (in === 3'b000) |-> (out === 8'b00000001)
    );

    // 001 selects bit 1.
    check_decode_001: assert property (
        @(posedge clk) (in === 3'b001) |-> (out === 8'b00000010)
    );

    // 010 selects bit 2.
    check_decode_010: assert property (
        @(posedge clk) (in === 3'b010) |-> (out === 8'b00000100)
    );

    // 011 selects bit 3.
    check_decode_011: assert property (
        @(posedge clk) (in === 3'b011) |-> (out === 8'b00001000)
    );

    // 100 selects bit 4.
    check_decode_100: assert property (
        @(posedge clk) (in === 3'b100) |-> (out === 8'b00010000)
    );

    // 101 selects bit 5.
    check_decode_101: assert property (
        @(posedge clk) (in === 3'b101) |-> (out === 8'b00100000)
    );

    // 110 selects bit 6.
    check_decode_110: assert property (
        @(posedge clk) (in === 3'b110) |-> (out === 8'b01000000)
    );

    // 111 selects bit 7.
    check_decode_111: assert property (
        @(posedge clk) (in === 3'b111) |-> (out === 8'b10000000)
    );

    // For known inputs, the output is one-hot.
    check_output_onehot: assert property (
        @(posedge clk) !$isunknown(in) |-> $onehot(out)
    );

    // For known inputs, the output matches a left-shifted decode.
    check_output_matches_shift: assert property (
        @(posedge clk) !$isunknown(in) |-> (out === (8'b00000001 << in))
    );

endmodule