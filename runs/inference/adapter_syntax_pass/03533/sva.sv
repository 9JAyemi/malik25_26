module my_module_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2,
    input logic X
);

    // X must match the RTL combinational equation.
    check_x_matches_rtl_equation: assert property (
        @($global_clock)
        X == ((A1 | (A2 & ~A3)) & B1)
    );

    // B1 low must force X low.
    check_b1_low_forces_x_low: assert property (
        @($global_clock)
        !B1 |-> !X
    );

    // A1 high must force X high when B1 is high.
    check_a1_high_forces_x_high: assert property (
        @($global_clock)
        (B1 && A1) |-> X
    );

    // A2 high with A3 low must force X high when B1 is high.
    check_a2_a3_high_forces_x_high: assert property (
        @($global_clock)
        (B1 && A2 && !A3) |-> X
    );

    // A2 low must not affect X when A3 is high and B1 is high.
    check_a2_low_ignored_when_a3_high: assert property (
        @($global_clock)
        (B1 && !A3 && !A2) |-> !X
    );

    // A3 high must not affect X when A2 is low and B1 is high.
    check_a3_high_ignored_when_a2_low: assert property (
        @($global_clock)
        (B1 && !A2 && A3) |-> !X
    );

    // X high requires B1 to be high.
    check_x_high_requires_b1_high: assert property (
        @($global_clock)
        X |-> B1
    );

    // X high requires A1 or the A2/A3 term to be high.
    check_x_high_requires_source_term: assert property (
        @($global_clock)
        X |-> (A1 || (A2 && !A3))
    );

endmodule