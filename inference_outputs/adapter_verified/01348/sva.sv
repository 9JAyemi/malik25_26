module karnaugh_map_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic E,
    input logic F
);

// F is 1 for 5'b00000.
    check_f_one_00000: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b00000) |-> (F == 1'b1)
    );

// F is 0 for 5'b00001.
    check_f_zero_00001: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b00001) |-> (F == 1'b0)
    );

// F is 0 for 5'b00011.
    check_f_zero_00011: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b00011) |-> (F == 1'b0)
    );

// F is 0 for 5'b00010.
    check_f_zero_00010: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b00010) |-> (F == 1'b0)
    );

// F is 0 for 5'b00110.
    check_f_zero_00110: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b00110) |-> (F == 1'b0)
    );

// F is 1 for 5'b00111.
    check_f_one_00111: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b00111) |-> (F == 1'b1)
    );

// F is 1 for 5'b00101.
    check_f_one_00101: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b00101) |-> (F == 1'b1)
    );

// F is 0 for 5'b00100.
    check_f_zero_00100: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b00100) |-> (F == 1'b0)
    );

// F is 0 for 5'b01100.
    check_f_zero_01100: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b01100) |-> (F == 1'b0)
    );

// F is 1 for 5'b01101.
    check_f_one_01101: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b01101) |-> (F == 1'b1)
    );

// F is 1 for 5'b01111.
    check_f_one_01111: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b01111) |-> (F == 1'b1)
    );

// F is 1 for 5'b01110.
    check_f_one_01110: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b01110) |-> (F == 1'b1)
    );

// F is 1 for 5'b01010.
    check_f_one_01010: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b01010) |-> (F == 1'b1)
    );

// F is 1 for 5'b01011.
    check_f_one_01011: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b01011) |-> (F == 1'b1)
    );

// F is 1 for 5'b01001.
    check_f_one_01001: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b01001) |-> (F == 1'b1)
    );

// F is 0 for 5'b01000.
    check_f_zero_01000: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b01000) |-> (F == 1'b0)
    );

// F is 1 for 5'b11000.
    check_f_one_11000: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b11000) |-> (F == 1'b1)
    );

// F is 0 for 5'b11001.
    check_f_zero_11001: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b11001) |-> (F == 1'b0)
    );

// F is 0 for 5'b11011.
    check_f_zero_11011: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b11011) |-> (F == 1'b0)
    );

// F is 0 for 5'b11010.
    check_f_zero_11010: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b11010) |-> (F == 1'b0)
    );

// F is 1 for 5'b11110.
    check_f_one_11110: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b11110) |-> (F == 1'b1)
    );

// F is 1 for 5'b11111.
    check_f_one_11111: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b11111) |-> (F == 1'b1)
    );

// F is 0 for 5'b11101.
    check_f_zero_11101: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b11101) |-> (F == 1'b0)
    );

// F is 0 for 5'b11100.
    check_f_zero_11100: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b11100) |-> (F == 1'b0)
    );

// F is 0 for 5'b10100.
    check_f_zero_10100: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b10100) |-> (F == 1'b0)
    );

// F is 0 for 5'b10101.
    check_f_zero_10101: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b10101) |-> (F == 1'b0)
    );

// F is 0 for 5'b10111.
    check_f_zero_10111: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b10111) |-> (F == 1'b0)
    );

// F is 0 for 5'b10110.
    check_f_zero_10110: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b10110) |-> (F == 1'b0)
    );

// F is 1 for 5'b10010.
    check_f_one_10010: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b10010) |-> (F == 1'b1)
    );

// F is 1 for 5'b10011.
    check_f_one_10011: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b10011) |-> (F == 1'b1)
    );

// F is 0 for 5'b10001.
    check_f_zero_10001: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b10001) |-> (F == 1'b0)
    );

// F is 0 for 5'b10000.
    check_f_zero_