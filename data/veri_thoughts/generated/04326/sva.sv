module sky130_fd_sc_ls__o221a_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

    // X matches the OR-OR-AND logic implemented in the RTL.
    check_x_logic_equation: assert property (
        @($global_clock) X == ((B2 | B1) & (A2 | A1) & C1)
    );

    // A low C1 input forces X low.
    check_c1_low_forces_x_low: assert property (
        @($global_clock) (C1 == 1'b0) |-> (X == 1'b0)
    );

    // Both A inputs low force X low.
    check_a_inputs_low_force_x_low: assert property (
        @($global_clock) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (X == 1'b0)
    );

    // Both B inputs low force X low.
    check_b_inputs_low_force_x_low: assert property (
        @($global_clock) ((B1 == 1'b0) && (B2 == 1'b0)) |-> (X == 1'b0)
    );

    // A high X requires C1 to be high.
    check_x_high_requires_c1: assert property (
        @($global_clock) (X == 1'b1) |-> (C1 == 1'b1)
    );

    // A high X requires at least one A input to be high.
    check_x_high_requires_a_term: assert property (
        @($global_clock) (X == 1'b1) |-> ((A1 == 1'b1) || (A2 == 1'b1))
    );

    // A high X requires at least one B input to be high.
    check_x_high_requires_b_term: assert property (
        @($global_clock) (X == 1'b1) |-> ((B1 == 1'b1) || (B2 == 1'b1))
    );

    // When all three product terms are high, X must be high.
    check_all_terms_high_drive_x_high: assert property (
        @($global_clock) ((C1 == 1'b1) && ((A1 == 1'b1) || (A2 == 1'b1)) && ((B1 == 1'b1) || (B2 == 1'b1))) |-> (X == 1'b1)
    );

endmodule