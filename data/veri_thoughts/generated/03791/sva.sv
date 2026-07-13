module sky130_fd_sc_ls__a2111o_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);

    // RTL has no native clock or reset; assertions use the formal global clock.

    // X must match the implemented OR/AND combinational function.
    check_function_equation: assert property (
        @($global_clock) disable iff (1'b0)
        X == (D1 | C1 | B1 | (A1 & A2))
    );

    // D1 high must drive X high.
    check_d1_forces_x_high: assert property (
        @($global_clock) disable iff (1'b0)
        D1 |-> X
    );

    // C1 high must drive X high.
    check_c1_forces_x_high: assert property (
        @($global_clock) disable iff (1'b0)
        C1 |-> X
    );

    // B1 high must drive X high.
    check_b1_forces_x_high: assert property (
        @($global_clock) disable iff (1'b0)
        B1 |-> X
    );

    // A1 and A2 high together must drive X high.
    check_a1_a2_force_x_high: assert property (
        @($global_clock) disable iff (1'b0)
        (A1 & A2) |-> X
    );

    // With all OR terms low, X must be low.
    check_no_active_terms_drive_x_low: assert property (
        @($global_clock) disable iff (1'b0)
        (!D1 && !C1 && !B1 && !(A1 && A2)) |-> !X
    );

    // A low X means every contributing term is low.
    check_x_low_implies_all_terms_low: assert property (
        @($global_clock) disable iff (1'b0)
        !X |-> (!D1 && !C1 && !B1 && !(A1 && A2))
    );

    // If B1, C1, and D1 are low, X high requires the A1/A2 AND term.
    check_x_high_requires_a1_a2_when_bcd_low: assert property (
        @($global_clock) disable iff (1'b0)
        (X && !D1 && !C1 && !B1) |-> (A1 && A2)
    );

endmodule