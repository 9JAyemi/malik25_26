module logic_circuit_assertions (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic X
);

    // X must match the implemented OR-of-ANDs function.
    check_x_function: assert property (
        @(posedge clk) X == ((A1 & A2) | (B1 & B2) | C1)
    );

    // C1 high must drive X high.
    check_c1_implies_x_high: assert property (
        @(posedge clk) C1 |-> X
    );

    // A1 and A2 high together must drive X high.
    check_a_pair_implies_x_high: assert property (
        @(posedge clk) (A1 & A2) |-> X
    );

    // B1 and B2 high together must drive X high.
    check_b_pair_implies_x_high: assert property (
        @(posedge clk) (B1 & B2) |-> X
    );

    // If all OR inputs are low, X must be low.
    check_all_terms_low_implies_x_low: assert property (
        @(posedge clk) (!C1 && !(A1 & A2) && !(B1 & B2)) |-> !X
    );

    // X low means none of the three OR terms are asserted.
    check_x_low_only_when_all_terms_low: assert property (
        @(posedge clk) !X |-> (!C1 && !(A1 & A2) && !(B1 & B2))
    );

endmodule