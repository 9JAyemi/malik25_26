module sky130_fd_sc_lp__a2111o_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);

    // X must match the implemented OR-of-terms equation.
    check_output_equation: assert property (
        @($global_clock) X == (C1 | B1 | D1 | (A1 & A2))
    );

    // C1 directly forces X high through the OR gate.
    check_c1_forces_x_high: assert property (
        @($global_clock) C1 |-> X
    );

    // B1 directly forces X high through the OR gate.
    check_b1_forces_x_high: assert property (
        @($global_clock) B1 |-> X
    );

    // D1 directly forces X high through the OR gate.
    check_d1_forces_x_high: assert property (
        @($global_clock) D1 |-> X
    );

    // The A1/A2 AND term forces X high when both are high.
    check_a1_a2_force_x_high: assert property (
        @($global_clock) (A1 && A2) |-> X
    );

    // X must be low when no OR input term is active.
    check_no_active_term_means_x_low: assert property (
        @($global_clock) (!C1 && !B1 && !D1 && !(A1 && A2)) |-> !X
    );

    // A low X means none of the OR input terms are active.
    check_x_low_implies_no_active_term: assert property (
        @($global_clock) !X |-> (!C1 && !B1 && !D1 && !(A1 && A2))
    );

    // If only the AND path can explain X high, both A1 and A2 must be high.
    check_x_high_without_direct_or_inputs_requires_and_term: assert property (
        @($global_clock) (X && !C1 && !B1 && !D1) |-> (A1 && A2)
    );

endmodule