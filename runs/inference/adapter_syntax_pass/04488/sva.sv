module bcd_converter_sva (
    input logic clk,
    input logic [3:0] D,
    input logic [7:0] BCD
);

    // D=0 maps to BCD=00000000.
    check_map_d0: assert property (
        @(posedge clk) (D == 4'h0) |-> (BCD == 8'h00)
    );

    // D=1 maps to BCD=00000001.
    check_map_d1: assert property (
        @(posedge clk) (D == 4'h1) |-> (BCD == 8'h01)
    );

    // D=2 maps to BCD=00000010.
    check_map_d2: assert property (
        @(posedge clk) (D == 4'h2) |-> (BCD == 8'h02)
    );

    // D=3 maps to BCD=00000011.
    check_map_d3: assert property (
        @(posedge clk) (D == 4'h3) |-> (BCD == 8'h03)
    );

    // D=4 maps to BCD=00000100.
    check_map_d4: assert property (
        @(posedge clk) (D == 4'h4) |-> (BCD == 8'h04)
    );

    // D=5 maps to BCD=00000101.
    check_map_d5: assert property (
        @(posedge clk) (D == 4'h5) |-> (BCD == 8'h05)
    );

    // D=6 maps to BCD=00000110.
    check_map_d6: assert property (
        @(posedge clk) (D == 4'h6) |-> (BCD == 8'h06)
    );

    // D=7 maps to BCD=00000111.
    check_map_d7: assert property (
        @(posedge clk) (D == 4'h7) |-> (BCD == 8'h07)
    );

    // D=8 maps to BCD=00001000.
    check_map_d8: assert property (
        @(posedge clk) (D == 4'h8) |-> (BCD == 8'h08)
    );

    // D=9 maps to BCD=00001001.
    check_map_d9: assert property (
        @(posedge clk) (D == 4'h9) |-> (BCD == 8'h09)
    );

    // D=10 maps to BCD=00010000.
    check_map_d10: assert property (
        @(posedge clk) (D == 4'hA) |-> (BCD == 8'h10)
    );

    // D=11 maps to BCD=00010001.
    check_map_d11: assert property (
        @(posedge clk) (D == 4'hB) |-> (BCD == 8'h11)
    );

    // D=12 maps to BCD=00010010.
    check_map_d12: assert property (
        @(posedge clk) (D == 4'hC) |-> (BCD == 8'h12)
    );

    // D=13 maps to BCD=00010011.
    check_map_d13: assert property (
        @(posedge clk) (D == 4'hD) |-> (BCD == 8'h13)
    );

    // D=14 maps to BCD=00010100.
    check_map_d14: assert property (
        @(posedge clk) (D == 4'hE) |-> (BCD == 8'h14)
    );

    // D=15 maps to BCD=00010101.
    check_map_d15: assert property (
        @(posedge clk) (D == 4'hF) |-> (BCD == 8'h15)
    );

endmodule