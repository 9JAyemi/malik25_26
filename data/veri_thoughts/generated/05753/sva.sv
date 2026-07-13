module Comparator_Equal_sva
#(parameter S = 1)
(
    input logic         clk,
    input logic [S-1:0] Data_A,
    input logic [S-1:0] Data_B,
    input logic         equal_sgn
);

    // RTL is combinational with no reset; clk is the sampling clock for assertions.

    // equal_sgn must be high whenever the two inputs are equal.
    check_output_high_on_equal_inputs: assert property (
        @(posedge clk) (Data_A == Data_B) |-> (equal_sgn == 1'b1)
    );

    // equal_sgn must be low whenever the two inputs are different.
    check_output_low_on_unequal_inputs: assert property (
        @(posedge clk) (Data_A != Data_B) |-> (equal_sgn == 1'b0)
    );

    // equal_sgn must exactly match the RTL compare expression, including X behavior.
    check_output_matches_rtl_expression: assert property (
        @(posedge clk) equal_sgn === ((Data_A == Data_B) ? 1'b1 : 1'b0)
    );

endmodule