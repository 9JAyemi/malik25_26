module sky130_fd_sc_ms__a211o_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // X must match the implemented OR-of-AND function.
    check_x_matches_function: assert property (
        @(posedge clk) X == ((A1 & A2) | B1 | C1)
    );

    // B1 high must force X high.
    check_b1_forces_x_high: assert property (
        @(posedge clk) B1 |-> X
    );

    // C1 high must force X high.
    check_c1_forces_x_high: assert property (
        @(posedge clk) C1 |-> X
    );

    // A1 and A2 high together must force X high.
    check_a1_a2_force_x_high: assert property (
        @(posedge clk) (A1 & A2) |-> X
    );

    // With B1 and C1 low, X reduces to the A1/A2 AND term.
    check_no_b1_c1_reduces_to_and: assert property (
        @(posedge clk) (!B1 && !C1) |-> (X == (A1 & A2))
    );

    // With A1 and A2 low, X reduces to the OR of B1 and C1.
    check_no_a1_a2_reduces_to_or: assert property (
        @(posedge clk) (!A1 && !A2) |-> (X == (B1 | C1))
    );

    // If X is low, both the AND term and both OR inputs must be low.
    check_x_low_requires_all_terms_low: assert property (
        @(posedge clk) !X |-> (!B1 && !C1 && !(A1 & A2))
    );

endmodule