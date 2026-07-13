module four_input_and_sva (
    input logic A1,
    input logic A2,
    input logic B1_N,
    input logic C1,
    output logic X
);
    // The logic is purely combinational, so we will use @(posedge clk) for assertions.

    // Check that X is correctly calculated as A1 & A2 & ~B1_N
    check_X_calculation: assert property (
        @(posedge clk) disable iff (!reset_n) (X == (A1 & A2 & ~B1_N))
    ) else $error("X calculation is incorrect");

    // Check that X is not driven by C1
    check_X_not_driven_by_C1: assert property (
        @(posedge clk) disable iff (!reset_n) (X != (A1 & A2 & ~C1))
    ) else $error("X is driven by C1");

endmodule