module sky130_fd_sc_lp__o22a_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // X matches the implemented OR-OR-AND function.
    check_x_function: assert property (
        @($global_clock) X == ((A1 | A2) & (B1 | B2))
    );

    // No active A-side input forces X low.
    check_a_side_inactive_forces_x_low: assert property (
        @($global_clock) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (X == 1'b0)
    );

    // No active B-side input forces X low.
    check_b_side_inactive_forces_x_low: assert property (
        @($global_clock) ((B1 == 1'b0) && (B2 == 1'b0)) |-> (X == 1'b0)
    );

    // Any active input on both sides drives X high.
    check_both_sides_active_drive_x_high: assert property (
        @($global_clock) ((A1 | A2) && (B1 | B2)) |-> (X == 1'b1)
    );

    // X high requires an active A-side input.
    check_x_high_requires_a_side_active: assert property (
        @($global_clock) (X == 1'b1) |-> ((A1 | A2) == 1'b1)
    );

    // X high requires an active B-side input.
    check_x_high_requires_b_side_active: assert property (
        @($global_clock) (X == 1'b1) |-> ((B1 | B2) == 1'b1)
    );

endmodule