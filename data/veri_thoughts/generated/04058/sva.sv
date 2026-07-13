module decoder_3to8_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic EN,
    input logic [7:0] Y
);

    // Disabled decoder drives all outputs low.
    check_disable_drives_zero: assert property (
        @(posedge clk) (!EN) |-> (Y == 8'b00000000)
    );

    // Input 000 selects bit 0 when enabled.
    check_decode_000: assert property (
        @(posedge clk) (EN && !A && !B && !C) |-> (Y == 8'b00000001)
    );

    // Input 001 selects bit 1 when enabled.
    check_decode_001: assert property (
        @(posedge clk) (EN && !A && !B && C) |-> (Y == 8'b00000010)
    );

    // Input 010 selects bit 2 when enabled.
    check_decode_010: assert property (
        @(posedge clk) (EN && !A && B && !C) |-> (Y == 8'b00000100)
    );

    // Input 011 selects bit 3 when enabled.
    check_decode_011: assert property (
        @(posedge clk) (EN && !A && B && C) |-> (Y == 8'b00001000)
    );

    // Input 100 selects bit 4 when enabled.
    check_decode_100: assert property (
        @(posedge clk) (EN && A && !B && !C) |-> (Y == 8'b00010000)
    );

    // Input 101 selects bit 5 when enabled.
    check_decode_101: assert property (
        @(posedge clk) (EN && A && !B && C) |-> (Y == 8'b00100000)
    );

    // Input 110 selects bit 6 when enabled.
    check_decode_110: assert property (
        @(posedge clk) (EN && A && B && !C) |-> (Y == 8'b01000000)
    );

    // Input 111 selects bit 7 when enabled.
    check_decode_111: assert property (
        @(posedge clk) (EN && A && B && C) |-> (Y == 8'b10000000)
    );

    // Enabled decoder output must be one-hot encoded.
    check_enabled_output_onehot: assert property (
        @(posedge clk) EN |-> (
            (Y == 8'b00000001) ||
            (Y == 8'b00000010) ||
            (Y == 8'b00000100) ||
            (Y == 8'b00001000) ||
            (Y == 8'b00010000) ||
            (Y == 8'b00100000) ||
            (Y == 8'b01000000) ||
            (Y == 8'b10000000)
        )
    );

endmodule