module my_module_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2,
    input logic X
);

    // X must match the implemented combinational equation.
    check_x_matches_equation: assert property (
        @(posedge clk) X == ((A1 | (A2 & ~A3)) & B1)
    );

    // B1 low forces X low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk) !B1 |-> !X
    );

    // A1 high forces X high.
    check_a1_high_forces_x_high: assert property (
        @(posedge clk) A1 |-> X
    );

    // A2 high with A3 low forces X high.
    check_a2_high_a3_low_forces_x_high: assert property (
        @(posedge clk) (A2 & ~A3) |-> X
    );

    // With B1 high, X reduces to A1 or (A2 & ~A3).
    check_b1_high_reduces_to_or: assert property (
        @(posedge clk) B1 |-> (X == (A1 | (A2 & ~A3)))
    );

    // With A1 low, X reduces to B1 & (A2 & ~A3).
    check_a1_low_reduces_to_and: assert property (
        @(posedge clk) !A1 |-> (X == (B1 & (A2 & ~A3)))
    );

    // With A2 low, X reduces to B1 & A1.
    check_a2_low_reduces_to_and: assert property (
        @(posedge clk) !A2 |-> (X == (B1 & A1))
    );

    // With A3 high, X reduces to B1 & A1.
    check_a3_high_reduces_to_and: assert property (
        @(posedge clk) A3 |-> (X == (B1 & A1))
    );

endmodule