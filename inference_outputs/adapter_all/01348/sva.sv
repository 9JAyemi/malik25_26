module karnaugh_map_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic E,
    input logic F
);

    // F is high for 00000, 00111, 00101, 01101, 01111, 01110, 01010, 01011, 01001, 11000, 11011, 11010, 11110, 11111, 10010.
    check_f_high_pattern: assert property (
        @(posedge clk)
        F == (
            ({A,B,C,D,E} == 5'b00000) ||
            ({A,B,C,D,E} == 5'b00111) ||
            ({A,B,C,D,E} == 5'b00101) ||
            ({A,B,C,D,E} == 5'b01101) ||
            ({A,B,C,D,E} == 5'b01111) ||
            ({A,B,C,D,E} == 5'b01110) ||
            ({A,B,C,D,E} == 5'b01010) ||
            ({A,B,C,D,E} == 5'b01011) ||
            ({A,B,C,D,E} == 5'b01001) ||
            ({A,B,C,D,E} == 5'b11000) ||
            ({A,B,C,D,E} == 5'b11011) ||
            ({A,B,C,D,E} == 5'b11010) ||
            ({A,B,C,D,E} == 5'b11110) ||
            ({A,B,C,D,E} == 5'b11111) ||
            ({A,B,C,D,E} == 5'b10010)
        )
    );

    // F is low for all other input patterns.
    check_f_low_other_patterns: assert property (
        @(posedge clk)
        !(
            ({A,B,C,D,E} == 5'b00000) ||
            ({A,B,C,D,E} == 5'b00111) ||
            ({A,B,C,D,E} == 5'b00101) ||
            ({A,B,C,D,E} == 5'b01101) ||
            ({A,B,C,D,E} == 5'b01111) ||
            ({A,B,C,D,E} == 5'b01110) ||
            ({A,B,C,D,E} == 5'b01010) ||
            ({A,B,C,D,E} == 5'b01011) ||
            ({A,B,C,D,E} == 5'b01001) ||
            ({A,B,C,D,E} == 5'b11000) ||
            ({A,B,C,D,E} == 5'b11011) ||
            ({A,B,C,D,E} == 5'b11010) ||
            ({A,B,C,D,E} == 5'b11110) ||
            ({A,B,C,D,E} == 5'b11111) ||
            ({A,B,C,D,E} == 5'b10010)
        ) |-> (F == 1'b0)
    );

    // F matches the implemented case table for all 32 input combinations.
    check_f_matches_case_table: assert property (
        @(posedge clk)
        F == (
            ({A,B,C,D,E} == 5'b00000) ||
            ({A,B,C,D,E} == 5'b00111) ||
            ({A,B,C,D,E} == 5'b00101) ||
            ({A,B,C,D,E} == 5'b01101) ||
            ({A,B,C,D,E} == 5'b01111) ||
            ({A,B,C,D,E} == 5'b01110) ||
            ({A,B,C,D,E} == 5'b01010) ||
            ({A,B,C,D,E} == 5'b01011) ||
            ({A,B,C,D,E} == 5'b01001) ||
            ({A,B,C,D,E} == 5'b11000) ||
            ({A,B,C,D,E} == 5'b11011) ||
            ({A,B,C,D,E} == 5'b11010) ||
            ({A,B,C,D,E} == 5'b11110) ||
            ({A,B,C,D,E} == 5'b11111) ||
            ({A,B,C,D,E} == 5'b10010)
        )
    );

endmodule