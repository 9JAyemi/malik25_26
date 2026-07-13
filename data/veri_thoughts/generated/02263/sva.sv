module hex_to_seven_seg_sva (
    input logic CLK,           // sampling clock (DUT has no clock/reset)
    input logic [3:0] B,       // hex digit input
    input logic [6:0] SSEG_L   // active-low segments GFEDCBA
);

    // B=0 maps to "0" glyph (active-low GFEDCBA)
    check_decode_b0: assert property (
        @(posedge CLK) (B == 4'h0) |=> (SSEG_L == 7'b1000000)
    );

    // B=1 maps to "1" glyph
    check_decode_b1: assert property (
        @(posedge CLK) (B == 4'h1) |=> (SSEG_L == 7'b1111001)
    );

    // B=2 maps to "2" glyph
    check_decode_b2: assert property (
        @(posedge CLK) (B == 4'h2) |=> (SSEG_L == 7'b0100100)
    );

    // B=3 maps to "3" glyph
    check_decode_b3: assert property (
        @(posedge CLK) (B == 4'h3) |=> (SSEG_L == 7'b0110000)
    );

    // B=4 maps to "4" glyph
    check_decode_b4: assert property (
        @(posedge CLK) (B == 4'h4) |=> (SSEG_L == 7'b0011001)
    );

    // B=5 maps to "5" glyph
    check_decode_b5: assert property (
        @(posedge CLK) (B == 4'h5) |=> (SSEG_L == 7'b0010010)
    );

    // B=6 maps to "6" glyph
    check_decode_b6: assert property (
        @(posedge CLK) (B == 4'h6) |=> (SSEG_L == 7'b0000010)
    );

    // B=7 maps to "7" glyph
    check_decode_b7: assert property (
        @(posedge CLK) (B == 4'h7) |=> (SSEG_L == 7'b1111000)
    );

    // B=8 maps to "8" glyph
    check_decode_b8: assert property (
        @(posedge CLK) (B == 4'h8) |=> (SSEG_L == 7'b0000000)
    );

    // B=9 maps to "9" glyph
    check_decode_b9: assert property (
        @(posedge CLK) (B == 4'h9) |=> (SSEG_L == 7'b0010000)
    );

    // B=A maps to "A" glyph
    check_decode_bA: assert property (
        @(posedge CLK) (B == 4'hA) |=> (SSEG_L == 7'b0001000)
    );

    // B=B maps to "b" glyph
    check_decode_bB: assert property (
        @(posedge CLK) (B == 4'hB) |=> (SSEG_L == 7'b0000011)
    );

    // B=C maps to "C" glyph
    check_decode_bC: assert property (
        @(posedge CLK) (B == 4'hC) |=> (SSEG_L == 7'b1000110)
    );

    // B=D maps to "d" glyph
    check_decode_bD: assert property (
        @(posedge CLK) (B == 4'hD) |=> (SSEG_L == 7'b0100001)
    );

    // B=E maps to "E" glyph
    check_decode_bE: assert property (
        @(posedge CLK) (B == 4'hE) |=> (SSEG_L == 7'b0000110)
    );

    // B=F maps to "F" glyph
    check_decode_bF: assert property (
        @(posedge CLK) (B == 4'hF) |=> (SSEG_L == 7'b0001110)
    );

endmodule