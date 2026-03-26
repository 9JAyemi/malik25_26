module four_input_module_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic X
);

    // External clk samples this combinational DUT; the RTL has no reset.
    // When A1 and A2 are both high, X must be high.
    check_a1_a2_sets_x: assert property (
        @(posedge clk) (A1 && A2) |-> (X == 1'b1)
    );

    // When A1 is high and A2 is low, X must be low.
    check_a1_without_a2_clears_x: assert property (
        @(posedge clk) (A1 && !A2) |-> (X == 1'b0)
    );

    // When A1 is low and B1 is high, X must be low.
    check_not_a1_b1_clears_x: assert property (
        @(posedge clk) (!A1 && B1) |-> (X == 1'b0)
    );

    // When the C1 branch is selected, X must be high.
    check_c1_branch_sets_x: assert property (
        @(posedge clk) (!A1 && !B1 && C1) |-> (X == 1'b1)
    );

    // When no branch condition is true, X must be low.
    check_default_branch_clears_x: assert property (
        @(posedge clk) (!A1 && !B1 && !C1) |-> (X == 1'b0)
    );

    // X must match the implemented combinational function.
    check_x_matches_function: assert property (
        @(posedge clk) X == ((A1 && A2) || (!A1 && !B1 && C1))
    );

endmodule