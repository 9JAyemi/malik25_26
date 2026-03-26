module my_module_assertions (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // C1 high makes the OR result and X high.
    check_c1_forces_x_high: assert property (
        @($global_clock) C1 |-> X
    );

    // B1 high makes the OR result and X high.
    check_b1_forces_x_high: assert property (
        @($global_clock) B1 |-> X
    );

    // D1 high makes the OR result and X high.
    check_d1_forces_x_high: assert property (
        @($global_clock) D1 |-> X
    );

    // A1 and A2 high together make X high through the AND path.
    check_and_path_forces_x_high: assert property (
        @($global_clock) (A1 && A2) |-> X
    );

    // With C1, B1, and D1 low, X follows only the A1&A2 term.
    check_isolated_and_path_behavior: assert property (
        @($global_clock) (!C1 && !B1 && !D1) |-> (X == (A1 && A2))
    );

    // When every contributing term is low, X must be low.
    check_all_terms_low_forces_x_low: assert property (
        @($global_clock) (!C1 && !B1 && !D1 && (!A1 || !A2)) |-> !X
    );

    // X matches the implemented combinational equation.
    check_full_boolean_equation: assert property (
        @($global_clock) X == (C1 || B1 || D1 || (A1 && A2))
    );

endmodule