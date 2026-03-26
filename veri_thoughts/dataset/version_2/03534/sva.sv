module my_module_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // X is the NOR of B1 and C1; A1 and A2 do not affect X.
    check_x_matches_nor_function: assert property (
        @(posedge clk) X == ~(B1 | C1)
    );

    // If both NOR inputs are low, X must be high.
    check_x_high_when_b1_c1_low: assert property (
        @(posedge clk) (!B1 && !C1) |-> X
    );

    // If B1 is high, X must be low.
    check_x_low_when_b1_high: assert property (
        @(posedge clk) B1 |-> !X
    );

    // If C1 is high, X must be low.
    check_x_low_when_c1_high: assert property (
        @(posedge clk) C1 |-> !X
    );

    // A high X means both NOR inputs are low.
    check_x_high_implies_b1_c1_low: assert property (
        @(posedge clk) X |-> (!B1 && !C1)
    );

    // A low X means at least one NOR input is high.
    check_x_low_implies_b1_or_c1_high: assert property (
        @(posedge clk) !X |-> (B1 || C1)
    );

    // Changing only A1/A2 while B1/C1 stay stable cannot change X.
    check_x_unchanged_when_only_a_inputs_change: assert property (
        @(posedge clk) (($changed(A1) || $changed(A2)) && $stable(B1) && $stable(C1)) |-> $stable(X)
    );

endmodule