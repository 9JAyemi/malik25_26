module bcd_converter_sva (
    input logic clk,
    input logic [3:0] D,
    input logic [7:0] BCD
);

// 0 maps to 00000000.
    check_map_0: assert property (
        @(posedge clk) (D == 4'h0) |-> (BCD == 8'h00)
    );

// 1 maps to 00000001.
    check_map_1: assert property (
        @(posedge clk) (D == 4'h1) |-> (BCD == 8'h01)
    );

// 2 maps to 00000010.
    check_map_2: assert property (
        @(posedge clk) (D == 4'h2) |-> (BCD == 8'h02)
    );

// 3 maps to 00000011.
    check_map_3: assert property (
        @(posedge clk) (D == 4'h3) |-> (BCD == 8'h03)
    );

// 4 maps to 00000100.
    check_map_4: assert property (
        @(posedge clk) (D == 4'h4) |-> (BCD == 8'h04)
    );

// 5 maps to 00000101.
    check_map_5: assert property (
        @(posedge clk) (D == 4'h5) |-> (BCD == 8'h05)
    );

// 6 maps to 00000110.
    check_map_6: assert property (
        @(posedge clk) (D == 4'h6) |-> (BCD == 8'h06)
    );

// 7 maps to 00000111.
    check_map_7: assert property (
        @(posedge clk) (D == 4'h7) |-> (BCD == 8'h07)
    );

// 8 maps to 00001000.
    check_map_8: assert property (
        @(posedge clk) (D == 4'h8) |-> (BCD == 8'h08)
    );

// 9 maps to 00001001.
    check_map_9: assert property (
        @(posedge clk) (D == 4'h9) |-> (BCD == 8'h09)
    );

// 10 maps to 00010000.
    check_map_10: assert property (
        @(posedge clk) (D == 4'hA) |-> (BCD == 8'h10)
    );

// 11 maps to 00010001.
    check_map_11: assert property (
        @(posedge clk) (D == 4'hB) |-> (BCD == 8'h11)
    );

// 12 maps to 00010010.
    check_map_12: assert property (
        @(posedge clk) (D == 4'hC) |-> (BCD == 8'h12)
    );

// 13 maps to 00010011.
    check_map_13: assert property (
        @(posedge clk) (D == 4'hD) |-> (BCD == 8'h13)
    );

// 14 maps to 00010100.
    check_map_14: assert property (
        @(posedge clk) (D == 4'hE) |-> (BCD == 8'h14)
    );

// 15 maps to 00010101.
    check_map_15: assert property (
        @(posedge clk) (D == 4'hF) |-> (BCD == 8'h15)
    );

// Output is always one of the exact encodings listed.
    check_output_encoding: assert property (
        @(posedge clk) 1'b1 |-> (
            (BCD == 8'h00) || (BCD == 8'h01) || (BCD == 8'h02) || (BCD == 8'h03) ||
            (BCD == 8'h04) || (BCD == 8'h05) || (BCD == 8'h06) || (BCD == 8'h07) ||
            (BCD == 8'h08) || (BCD == 8'h09) || (BCD == 8'h10) || (BCD == 8'h11) ||
            (BCD == 8'h12) || (BCD == 8'h13) || (BCD == 8'h14) || (BCD == 8'h15)
        )
    );

endmodule
