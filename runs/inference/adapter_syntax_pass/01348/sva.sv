module karnaugh_map_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic E,
    input logic F
);

    // F is high for 00000 and 01111.
    check_f_high_for_00000_01111: assert property (
        @(posedge clk) (({A,B,C,D,E} == 5'b00000) || ({A,B,C,D,E} == 5'b01111)) |-> (F == 1'b1)
    );

    // F is low for 00001, 00011, 00010, 00110, 00111, 00101, 00100, 01100, 01101, 01010, 01011, 01001, 01000, 11000, 11001, 11011, 11010, 11100, 11101, 10100, 10101, 10111, 10110, 10000, 10001, 10010, 10011, and 11110.
    check_f_low_for_specific_codes: assert property (
        @(posedge clk)
        (({A,B,C,D,E} == 5'b00001) || ({A,B,C,D,E} == 5'b00011) || ({A,B,C,D,E} == 5'b00010) || ({A,B,C,D,E} == 5'b00110) || ({A,B,C,D,E} == 5'b00111) || ({A,B,C,D,E} == 5'b00101) || ({A,B,C,D,E} == 5'b00100) || ({A,B,C,D,E} == 5'b01100) || ({A,B,C,D,E} == 5'b01101) || ({A,B,C,D,E} == 5'b01010) || ({A,B,C,D,E} == 5'b01011) || ({A,B,C,D,E} == 5'b01001) || ({A,B,C,D,E} == 5'b01000) || ({A,B,C,D,E} == 5'b11000) || ({A,B,C,D,E} == 5'b11001) || ({A,B,C,D,E} == 5'b11011) || ({A,B,C,D,E} == 5'b11010) || ({A,B,C,D,E} == 5'b11100) || ({A,B,C,D,E} == 5'b11101) || ({A,B,C,D,E} == 5'b10100) || ({A,B,C,D,E} == 5'b10101) || ({A,B,C,D,E} == 5'b10111) || ({A,B,C,D,E} == 5'b10110) || ({A,B,C,D,E} == 5'b10000) || ({A,B,C,D,E} == 5'b10001) || ({A,B,C,D,E} == 5'b10010) || ({A,B,C,D,E} == 5'b10011) || ({A,B,C,D,E} == 5'b11110))
        |-> (F == 1'b0)
    );

    // F is high for 11111.
    check_f_high_for_11111: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b11111) |-> (F == 1'b1)
    );

    // F is low for 11110.
    check_f_low_for_11110: assert property (
        @(posedge clk) ({A,B,C,D,E} == 5'b11110) |-> (F == 1'b0)
    );

    // F is high for 10011 and 10010.
    check_f_high_for_10011_10010: assert property (
        @(posedge clk) (({A,B,C,D,E} == 5'b10011) || ({A,B,C,D,E} == 5'b10010)) |-> (F == 1'b1)
    );

    // F is low for 10001, 10000, 10100, 10101, 10111, 10110, 11000, 11001, 11011, 11010, 11100, 11101, 00001, 00011, 00010, 00110, 00111, 00101, 00100, 01100, 01101, 01010, 01011, 01001, 01000, and 10001.
    check_f_low_for_remaining_codes: assert property (
        @(posedge clk)
        (({A,B,C,D,E} == 5'b10001) || ({A,B,C,D,E} == 5'b10000) || ({A,B,C,D,E} == 5'b10100) || ({A,B,C,D,E} == 5'b10101) || ({A,B,C,D,E} == 5'b10111) || ({A,B,C,D,E} == 5'b10110) || ({A,B,C,D,E} == 5'b11000) || ({A,B,C,D,E} == 5'b11001) || ({A,B,C,D,E} == 5'b11011) || ({A,B,C,D,E} == 5'b11010) || ({A,B,C,D,E} == 5'b11100) || ({A,B,C,D,E} == 5'b11101) || ({A,B,C,D,E} == 5'b00001) || ({A,B,C,D,E} == 5'b00011) || ({A,B,C,D,E} == 5'b00010) || ({A,B,C,D,E} == 5'b00110) || ({A,B,C,D,E} == 5'b00111) || ({A,B,C,D,E} == 5'b00101) || ({A,B,C,D,E} == 5'b00100) || ({A,B,C,D,E} == 5'b01100) || ({A,B,C,D,E} == 5'b01101) || ({A,B,C,D,E} == 5'b01010) || ({A,B,C,D,E} == 5'b01011) || ({A,B,C,D,E} == 5'b01001) || ({A,B,C,D,E} == 5'b01000))
        |-> (F == 1'b0)
    );

endmodule