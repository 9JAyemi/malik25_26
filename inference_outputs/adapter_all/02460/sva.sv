module sky130_fd_sc_ls__o2111a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);

    // X must match the implemented OR-then-AND function.
    check_x_matches_function: assert property (
        @(posedge clk) X == (B1 & C1 & D1 & (A1 | A2))
    );

    // B1 low forces X low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk) !B1 |-> !X
    );

    // C1 low forces X low.
    check_c1_low_forces_x_low: assert property (
        @(posedge clk) !C1 |-> !X
    );

    // D1 low forces X low.
    check_d1_low_forces_x_low: assert property (
        @(posedge clk) !D1 |-> !X
    );

    // Both A inputs low force X low.
    check_a_inputs_low_force_x_low: assert property (
        @(posedge clk) !(A1 | A2) |-> !X
    );

    // With all required terms high, X must be high.
    check_all_terms_high_drive_x_high: assert property (
        @(posedge clk) (B1 & C1 & D1 & (A1 | A2)) |-> X
    );

    // X high requires B1, C1, and D1 high.
    check_x_high_requires_required_terms: assert property (
        @(posedge clk) X |-> (B1 & C1 & D1)
    );

    // X high requires at least one A input high.
    check_x_high_requires_a_term: assert property (
        @(posedge clk) X |-> (A1 | A2)
    );

endmodule