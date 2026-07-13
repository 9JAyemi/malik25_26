module decoder_3to8_sva (
    input logic clk,
    input logic [2:0] in,
    input logic [7:0] out
);

    // Input 000 drives only bit 0 low.
    check_decode_000: assert property (
        @(posedge clk) (in == 3'b000) |-> (out == 8'b11111110)
    );

    // Input 001 drives only bit 1 low.
    check_decode_001: assert property (
        @(posedge clk) (in == 3'b001) |-> (out == 8'b11111101)
    );

    // Input 010 drives only bit 2 low.
    check_decode_010: assert property (
        @(posedge clk) (in == 3'b010) |-> (out == 8'b11111011)
    );

    // Input 011 drives only bit 3 low.
    check_decode_011: assert property (
        @(posedge clk) (in == 3'b011) |-> (out == 8'b11110111)
    );

    // Input 100 drives only bit 4 low.
    check_decode_100: assert property (
        @(posedge clk) (in == 3'b100) |-> (out == 8'b11101111)
    );

    // Input 101 drives only bit 5 low.
    check_decode_101: assert property (
        @(posedge clk) (in == 3'b101) |-> (out == 8'b11011111)
    );

    // Input 110 drives only bit 6 low.
    check_decode_110: assert property (
        @(posedge clk) (in == 3'b110) |-> (out == 8'b10111111)
    );

    // Input 111 drives only bit 7 low.
    check_decode_111: assert property (
        @(posedge clk) (in == 3'b111) |-> (out == 8'b01111111)
    );

    // Known inputs produce an active-low one-hot output.
    check_active_low_onehot: assert property (
        @(posedge clk) !$isunknown(in) |-> $onehot(~out)
    );

    // Unknown input bits select the default all-high output.
    check_default_unknown_input: assert property (
        @(posedge clk) $isunknown(in) |-> (out == 8'b11111111)
    );

endmodule