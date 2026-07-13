module functional_module_sva (
    input logic [3:0] B,
    input logic [1:0] in,
    input logic [15:0] out
);

    // out must always be one-hot.
    check_out_onehot: assert property (
        @($global_clock) $onehot(out)
    );

    // in=00 selects bit 0.
    check_decode_in00: assert property (
        @($global_clock) (in == 2'b00) |-> (out == 16'h0001)
    );

    // in=01 selects bit 1.
    check_decode_in01: assert property (
        @($global_clock) (in == 2'b01) |-> (out == 16'h0002)
    );

    // in=10 selects bit 2.
    check_decode_in10: assert property (
        @($global_clock) (in == 2'b10) |-> (out == 16'h0004)
    );

    // in=11 selects bit 3.
    check_decode_in11: assert property (
        @($global_clock) (in == 2'b11) |-> (out == 16'h0008)
    );

    // B=0000 maps to E=0011, so out must be bit 3.
    check_map_0000: assert property (
        @($global_clock) (B == 4'h0) |-> (out == 16'h0008)
    );

    // B=0001 maps to E=0100, so out must be bit 4.
    check_map_0001: assert property (
        @($global_clock) (B == 4'h1) |-> (out == 16'h0010)
    );

    // B=0010 maps to E=0101, so out must be bit 5.
    check_map_0010: assert property (
        @($global_clock) (B == 4'h2) |-> (out == 16'h0020)
    );

    // B=0011 maps to E=0110, so out must be bit 6.
    check_map_0011: assert property (
        @($global_clock) (B == 4'h3) |-> (out == 16'h0040)
    );

    // B=0100 maps to E=0111, so out must be bit 7.
    check_map_0100: assert property (
        @($global_clock) (B == 4'h4) |-> (out == 16'h0080)
    );

    // B=0101 maps to E=1000, so out must be bit 8.
    check_map_0101: assert property (
        @($global_clock) (B == 4'h5) |-> (out == 16'h0100)
    );

    // B=0110 maps to E=1001, so out must be bit 9.
    check_map_0110: assert property (
        @($global_clock) (B == 4'h6) |-> (out == 16'h0200)
    );

    // B=0111 maps to E=1010, so out must be bit 10.
    check_map_0111: assert property (
        @($global_clock) (B == 4'h7) |-> (out == 16'h0400)
    );

    // B=1000 maps to E=1011, so out must be bit 11.
    check_map_1000: assert property (
        @($global_clock) (B == 4'h8) |-> (out == 16'h0800)
    );

    // B=1001 maps to E=1100, so out must be bit 12.
    check_map_1001: assert property (
        @($global_clock) (B == 4'h9) |-> (out == 16'h1000)
    );

    // B=1010 maps to E=1101, so out must be bit 1.
    check_map_1010: assert property (
        @($global_clock) (B == 4'hA) |-> (out == 16'h0002)
    );

    // B=1011 maps to E=1110, so out must be bit 2.
    check_map_1011: assert property (
        @($global_clock) (B == 4'hB) |-> (out == 16'h0004)
    );

    // B=1100 maps to E=1111, so out must be bit 3.
    check_map_1100: assert property (
        @($global_clock) (B == 4'hC) |-> (out == 16'h0008)
    );

    // B=1101 maps to E=0001, so out must be bit 13.
    check_map_1101: assert property (
        @($global_clock) (B == 4'hD) |-> (out == 16'h2000)
    );

    // B=1110 maps to E=0010, so out must be bit 14.
    check_map_1110: assert property (
        @($global_clock) (B == 4'hE) |-> (out == 16'h4000)
    );

    // B=1111 maps to E=0011, so out must be bit 15.
    check_map_1111: assert property (
        @($global_clock) (B == 4'hF) |-> (out == 16'h8000)
    );

endmodule