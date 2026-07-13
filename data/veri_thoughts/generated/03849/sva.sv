module sky130_fd_sc_lp__o2111a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);

    // X implements the OR-then-AND logic function.
    check_x_matches_logic_function: assert property (
        @(posedge clk) X == ((A1 || A2) && B1 && C1 && D1)
    );

    // A high X requires B1 to be high.
    check_x_high_requires_b1: assert property (
        @(posedge clk) X |-> B1
    );

    // A high X requires C1 to be high.
    check_x_high_requires_c1: assert property (
        @(posedge clk) X |-> C1
    );

    // A high X requires D1 to be high.
    check_x_high_requires_d1: assert property (
        @(posedge clk) X |-> D1
    );

    // A high X requires at least one A input to be high.
    check_x_high_requires_a1_or_a2: assert property (
        @(posedge clk) X |-> (A1 || A2)
    );

    // All required terms high drive X high.
    check_all_terms_high_drive_x: assert property (
        @(posedge clk) ((A1 || A2) && B1 && C1 && D1) |-> X
    );

    // If both A inputs are low, X must be low.
    check_both_a_inputs_low_force_x_low: assert property (
        @(posedge clk) (!A1 && !A2) |-> !X
    );

    // If B1 is low, X must be low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk) !B1 |-> !X
    );

    // If C1 is low, X must be low.
    check_c1_low_forces_x_low: assert property (
        @(posedge clk) !C1 |-> !X
    );

    // If D1 is low, X must be low.
    check_d1_low_forces_x_low: assert property (
        @(posedge clk) !D1 |-> !X
    );

endmodule