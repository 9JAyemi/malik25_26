module karnaugh_map_sva (
    input logic clk,        // sampling clock for SVA only (RTL has no clock/reset)
    input logic A, B, C, D, E,
    input logic F
);
    // F=0 for 00000
    check_map_00000_is_0: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b00000) |-> (F == 1'b0)
    );
    // F=1 for 00001
    check_map_00001_is_1: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b00001) |-> (F == 1'b1)
    );
    // F=1 for 00011
    check_map_00011_is_1: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b00011) |-> (F == 1'b1)
    );
    // F=0 for 00010
    check_map_00010_is_0: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b00010) |-> (F == 1'b0)
    );
    // F=1 for 00110
    check_map_00110_is_1: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b00110) |-> (F == 1'b1)
    );
    // F=0 for 00111
    check_map_00111_is_0: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b00111) |-> (F == 1'b0)
    );
    // F=1 for 00101
    check_map_00101_is_1: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b00101) |-> (F == 1'b1)
    );
    // F=0 for 00100
    check_map_00100_is_0: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b00100) |-> (F == 1'b0)
    );
    // F=1 for 01100
    check_map_01100_is_1: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b01100) |-> (F == 1'b1)
    );
    // F=0 for 01101
    check_map_01101_is_0: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b01101) |-> (F == 1'b0)
    );
    // F=1 for 01111
    check_map_01111_is_1: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b01111) |-> (F == 1'b1)
    );
    // F=0 for 01110
    check_map_01110_is_0: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b01110) |-> (F == 1'b0)
    );
    // F=1 for 01010
    check_map_01010_is_1: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b01010) |-> (F == 1'b1)
    );
    // F=0 for 01011
    check_map_01011_is_0: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b01011) |-> (F == 1'b0)
    );
    // F=1 for 01001
    check_map_01001_is_1: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b01001) |-> (F == 1'b1)
    );
    // F=0 for 01000
    check_map_01000_is_0: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b01000) |-> (F == 1'b0)
    );
    // F=1 for 11000
    check_map_11000_is_1: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b11000) |-> (F == 1'b1)
    );
    // F=0 for 11001
    check_map_11001_is_0: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b11001) |-> (F == 1'b0)
    );
    // F=1 for 11011
    check_map_11011_is_1: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b11011) |-> (F == 1'b1)
    );
    // F=0 for 11010
    check_map_11010_is_0: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b11010) |-> (F == 1'b0)
    );
    // F=1 for 11110
    check_map_11110_is_1: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b11110) |-> (F == 1'b1)
    );
    // F=0 for 11111
    check_map_11111_is_0: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b11111) |-> (F == 1'b0)
    );
    // F=1 for 11101
    check_map_11101_is_1: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b11101) |-> (F == 1'b1)
    );
    // F=0 for 11100
    check_map_11100_is_0: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b11100) |-> (F == 1'b0)
    );
    // F=1 for 10100
    check_map_10100_is_1: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b10100) |-> (F == 1'b1)
    );
    // F=0 for 10101
    check_map_10101_is_0: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b10101) |-> (F == 1'b0)
    );
    // F=1 for 10111
    check_map_10111_is_1: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b10111) |-> (F == 1'b1)
    );
    // F=0 for 10110
    check_map_10110_is_0: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b10110) |-> (F == 1'b0)
    );
    // F=1 for 10010
    check_map_10010_is_1: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b10010) |-> (F == 1'b1)
    );
    // F=0 for 10011
    check_map_10011_is_0: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b10011) |-> (F == 1'b0)
    );
    // F=1 for 10001
    check_map_10001_is_1: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b10001) |-> (F == 1'b1)
    );
    // F=0 for 10000
    check_map_10000_is_0: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b10000) |-> (F == 1'b0)
    );
endmodule