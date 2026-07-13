module Convierte_sva (
    input logic clk,
    input logic [3:0] Ver,
    input logic [6:0] Salida7seg
);
    // Ver=0 maps to 7-seg 000_0001
    check_decode_0: assert property (
        @(posedge clk) disable iff (1'b0) (Ver == 4'h0) |-> (Salida7seg == 7'b000_0001)
    );
    // Ver=1 maps to 7-seg 100_1111
    check_decode_1: assert property (
        @(posedge clk) disable iff (1'b0) (Ver == 4'h1) |-> (Salida7seg == 7'b100_1111)
    );
    // Ver=2 maps to 7-seg 001_0010
    check_decode_2: assert property (
        @(posedge clk) disable iff (1'b0) (Ver == 4'h2) |-> (Salida7seg == 7'b001_0010)
    );
    // Ver=3 maps to 7-seg 000_0110
    check_decode_3: assert property (
        @(posedge clk) disable iff (1'b0) (Ver == 4'h3) |-> (Salida7seg == 7'b000_0110)
    );
    // Ver=4 maps to 7-seg 100_1100
    check_decode_4: assert property (
        @(posedge clk) disable iff (1'b0) (Ver == 4'h4) |-> (Salida7seg == 7'b100_1100)
    );
    // Ver=5 maps to 7-seg 010_0100
    check_decode_5: assert property (
        @(posedge clk) disable iff (1'b0) (Ver == 4'h5) |-> (Salida7seg == 7'b010_0100)
    );
    // Ver=6 maps to 7-seg 010_0000
    check_decode_6: assert property (
        @(posedge clk) disable iff (1'b0) (Ver == 4'h6) |-> (Salida7seg == 7'b010_0000)
    );
    // Ver=7 maps to 7-seg 000_1111
    check_decode_7: assert property (
        @(posedge clk) disable iff (1'b0) (Ver == 4'h7) |-> (Salida7seg == 7'b000_1111)
    );
    // Ver=8 maps to 7-seg 000_0000
    check_decode_8: assert property (
        @(posedge clk) disable iff (1'b0) (Ver == 4'h8) |-> (Salida7seg == 7'b000_0000)
    );
    // Ver=9 maps to 7-seg 000_0100
    check_decode_9: assert property (
        @(posedge clk) disable iff (1'b0) (Ver == 4'h9) |-> (Salida7seg == 7'b000_0100)
    );
    // Ver=10 maps to 7-seg 000_1000
    check_decode_A: assert property (
        @(posedge clk) disable iff (1'b0) (Ver == 4'hA) |-> (Salida7seg == 7'b000_1000)
    );
    // Ver=11 maps to 7-seg 110_0000
    check_decode_b: assert property (
        @(posedge clk) disable iff (1'b0) (Ver == 4'hB) |-> (Salida7seg == 7'b110_0000)
    );
    // Ver=12 maps to 7-seg 011_0001
    check_decode_C: assert property (
        @(posedge clk) disable iff (1'b0) (Ver == 4'hC) |-> (Salida7seg == 7'b011_0001)
    );
    // Ver=13 maps to 7-seg 100_0012 (note: 0010 in RTL)
    check_decode_d: assert property (
        @(posedge clk) disable iff (1'b0) (Ver == 4'hD) |-> (Salida7seg == 7'b100_0010)
    );
    // Ver=14 maps to 7-seg 011_0000
    check_decode_E: assert property (
        @(posedge clk) disable iff (1'b0) (Ver == 4'hE) |-> (Salida7seg == 7'b011_0000)
    );
    // Ver=15 maps to 7-seg 011_1000
    check_decode_F: assert property (
        @(posedge clk) disable iff (1'b0) (Ver == 4'hF) |-> (Salida7seg == 7'b011_1000)
    );
endmodule