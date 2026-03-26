module sky130_fd_sc_lp__o2111a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);

    // X must match the implemented O2111A logic equation.
    check_x_equation: assert property (
        @(posedge clk) X == (B1 & C1 & D1 & (A1 | A2))
    );

    // When all product terms are true, X must be high.
    check_all_terms_true_drive_x_high: assert property (
        @(posedge clk) (B1 & C1 & D1 & (A1 | A2)) |-> X
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

    // If both A inputs are low, X must be low.
    check_a_inputs_low_force_x_low: assert property (
        @(posedge clk) (!A1 & !A2) |-> !X
    );

    // A high output requires all AND-side inputs to be high.
    check_x_high_requires_and_inputs: assert property (
        @(posedge clk) X |-> (B1 & C1 & D1)
    );

    // A high output requires at least one A input to be high.
    check_x_high_requires_or_input: assert property (
        @(posedge clk) X |-> (A1 | A2)
    );

endmodule