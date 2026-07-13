module Multiplexer_4to1_sva (
    input logic clk,
    input logic ctrl0,
    input logic ctrl1,
    input logic [0:0] D0,
    input logic [0:0] D1,
    input logic [0:0] D2,
    input logic [0:0] D3,
    input logic [0:0] S
);

    // Combinational DUT; clk is a sampling clock and there is no reset.

    // Select 00 routes D0 to S.
    check_select_00_routes_d0: assert property (
        @(posedge clk) ({ctrl1, ctrl0} === 2'b00) |-> (S === D0)
    );

    // Select 01 routes D1 to S.
    check_select_01_routes_d1: assert property (
        @(posedge clk) ({ctrl1, ctrl0} === 2'b01) |-> (S === D1)
    );

    // Select 10 routes D2 to S.
    check_select_10_routes_d2: assert property (
        @(posedge clk) ({ctrl1, ctrl0} === 2'b10) |-> (S === D2)
    );

    // Select 11 routes D3 to S.
    check_select_11_routes_d3: assert property (
        @(posedge clk) ({ctrl1, ctrl0} === 2'b11) |-> (S === D3)
    );

endmodule

module LUT4_sva (
    input logic clk,
    input logic [3:0] I,
    input logic O
);

    // Combinational DUT; clk is a sampling clock and there is no reset.

    // These input patterns drive O high in the implemented truth table.
    check_high_output_patterns: assert property (
        @(posedge clk)
        ((I === 4'b0000) || (I === 4'b0010) || (I === 4'b0100) || (I === 4'b0110) ||
         (I === 4'b1001) || (I === 4'b1011) || (I === 4'b1101) || (I === 4'b1111))
        |-> (O === 1'b1)
    );

    // These input patterns drive O low in the implemented truth table.
    check_low_output_patterns: assert property (
        @(posedge clk)
        ((I === 4'b0001) || (I === 4'b0011) || (I === 4'b0101) || (I === 4'b0111) ||
         (I === 4'b1000) || (I === 4'b1010) || (I === 4'b1100) || (I === 4'b1110))
        |-> (O === 1'b0)
    );

endmodule