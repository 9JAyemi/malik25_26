module logic_module_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    input logic X
);

    // X must match the implemented combinational equation.
    check_x_matches_logic: assert property (
        @($global_clock)
        X == ((A1 | A2) & (~B1 | B2) & (~A1 | ~A2 | B1))
    );

    // A1 high forces X high.
    check_a1_forces_x_high: assert property (
        @($global_clock)
        A1 |-> X
    );

    // A2 high forces X high.
    check_a2_forces_x_high: assert property (
        @($global_clock)
        A2 |-> X
    );

    // B1 low forces X low.
    check_b1_low_forces_x_low: assert property (
        @($global_clock)
        !B1 |-> !X
    );

    // B2 low forces X low.
    check_b2_low_forces_x_low: assert property (
        @($global_clock)
        !B2 |-> !X
    );

    // A1 and A2 high force X high.
    check_a1_a2_force_x_high: assert property (
        @($global_clock)
        (A1 && A2) |-> X
    );

    // B1 high with either A input low forces X high.
    check_b1_with_a_low_force_x_high: assert property (
        @($global_clock)
        (B1 && (!A1 || !A2)) |-> X
    );

    // X high requires at least one A input high.
    check_x_high_requires_a_input: assert property (
        @($global_clock)
        X |-> (A1 || A2)
    );

    // X high requires B1 low or B2 high.
    check_x_high_requires_b_term: assert property (
        @($global_clock)
        X |-> (!B1 || B2)
    );

    // X high requires A1 low or A2 low or B1 high.
    check_x_high_requires_a1_a2_or_b1: assert property (
        @($global_clock)
        X |-> (!A1 || !A2 || B1)
    );

endmodule