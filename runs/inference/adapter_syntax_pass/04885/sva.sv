module sky130_fd_sc_ls__o211a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // X matches the implemented OR-then-AND function.
    check_function_equivalence: assert property (
        @(posedge clk) X == ((A1 | A2) & B1 & C1)
    );

    // B1 low forces X low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk) !B1 |-> !X
    );

    // C1 low forces X low.
    check_c1_low_forces_x_low: assert property (
        @(posedge clk) !C1 |-> !X
    );

    // Both A inputs low force X low.
    check_a_inputs_low_force_x_low: assert property (
        @(posedge clk) (!A1 && !A2) |-> !X
    );

    // X high requires B1 and C1 high.
    check_x_high_requires_b1_and_c1: assert property (
        @(posedge clk) X |-> (B1 && C1)
    );

    // X high requires at least one A input high.
    check_x_high_requires_a1_or_a2: assert property (
        @(posedge clk) X |-> (A1 || A2)
    );

    // X high requires both OR and AND terms to be true.
    check_x_high_requires_both_terms: assert property (
        @(posedge clk) X |-> (((A1 | A2) & B1) && C1)
    );

endmodule