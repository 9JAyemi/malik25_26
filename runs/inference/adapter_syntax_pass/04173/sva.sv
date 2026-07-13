module logic_module_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    input logic X
);

    // X must match the RTL boolean equation.
    check_x_matches_rtl_equation: assert property (
        @($global_clock)
        X == ((A1 | A2) & (~B1 | B2) & (~A1 | ~A2 | B1))
    );

    // A1 high must force X high.
    check_a1_forces_x_high: assert property (
        @($global_clock)
        A1 |-> X
    );

    // A2 high must force X high.
    check_a2_forces_x_high: assert property (
        @($global_clock)
        A2 |-> X
    );

    // B1 low must force X low.
    check_b1_low_forces_x_low: assert property (
        @($global_clock)
        !B1 |-> !X
    );

    // B2 low with A1 low must force X low.
    check_b2_low_and_a1_low_force_x_low: assert property (
        @($global_clock)
        (!B2 && !A1) |-> !X
    );

    // B2 low with A2 low must force X low.
    check_b2_low_and_a2_low_force_x_low: assert property (
        @($global_clock)
        (!B2 && !A2) |-> !X
    );

    // A1 and A2 high must force X high.
    check_a1_a2_high_force_x_high: assert property (
        @($global_clock)
        (A1 && A2) |-> X
    );

    // B1 high with A1 low must force X high.
    check_b1_high_and_a1_low_force_x_high: assert property (
        @($global_clock)
        (B1 && !A1) |-> X
    );

    // B1 high with A2 low must force X high.
    check_b1_high_and_a2_low_force_x_high: assert property (
        @($global_clock)
        (B1 && !A2) |-> X
    );

    // B2 high with A1 low must force X low.
    check_b2_high_and_a1_low_force_x_low: assert property (
        @($global_clock)
        (B2 && !A1) |-> !X
    );

    // B2 high with A2 low must force X low.
    check_b2_high_and_a2_low_force_x_low: assert property (
        @($global_clock)
        (B2 && !A2) |-> !X
    );

endmodule