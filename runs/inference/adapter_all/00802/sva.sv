module my_or4b_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D_N
);

    // X matches the implemented OR-of-terms function.
    check_x_matches_function: assert property (
        @(posedge clk) X == (A | B | C | ~D_N)
    );

    // A high forces X high.
    check_a_high_forces_x_high: assert property (
        @(posedge clk) A |-> X
    );

    // B high forces X high.
    check_b_high_forces_x_high: assert property (
        @(posedge clk) B |-> X
    );

    // C high forces X high.
    check_c_high_forces_x_high: assert property (
        @(posedge clk) C |-> X
    );

    // D_N low forces X high.
    check_d_n_low_forces_x_high: assert property (
        @(posedge clk) !D_N |-> X
    );

    // With all OR terms low, X must be low.
    check_all_terms_low_forces_x_low: assert property (
        @(posedge clk) (!A && !B && !C && D_N) |-> !X
    );

    // X low implies all OR terms are low.
    check_x_low_implies_all_terms_low: assert property (
        @(posedge clk) !X |-> (!A && !B && !C && D_N)
    );

endmodule