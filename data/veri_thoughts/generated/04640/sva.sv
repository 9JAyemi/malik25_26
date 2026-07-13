module sky130_fd_sc_lp__o41a_m_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // No explicit clock or reset exists in the RTL; sample on the global clock.
    // The logic is purely combinational and X depends only on A1, A2, A4, and B1.

    // X matches the implemented 4-input AND function.
    check_x_matches_function: assert property (
        @($global_clock) X == (A1 & A2 & A4 & B1)
    );

    // All controlling inputs high drive X high.
    check_all_controls_high_drive_x: assert property (
        @($global_clock) (A1 & A2 & A4 & B1) |-> X
    );

    // A low A1 forces X low.
    check_a1_low_forces_x_low: assert property (
        @($global_clock) !A1 |-> !X
    );

    // A low A2 forces X low.
    check_a2_low_forces_x_low: assert property (
        @($global_clock) !A2 |-> !X
    );

    // A low A4 forces X low.
    check_a4_low_forces_x_low: assert property (
        @($global_clock) !A4 |-> !X
    );

    // A low B1 forces X low.
    check_b1_low_forces_x_low: assert property (
        @($global_clock) !B1 |-> !X
    );

    // A3 is unused in the logic that drives X.
    check_a3_change_does_not_affect_x: assert property (
        @($global_clock)
        ($stable(A1) && $stable(A2) && $stable(A4) && $stable(B1) && $changed(A3)) |-> $stable(X)
    );

    // Power pins are not referenced in the RTL logic for X.
    check_power_pin_changes_do_not_affect_x: assert property (
        @($global_clock)
        ($stable(A1) && $stable(A2) && $stable(A4) && $stable(B1) &&
         ($changed(VPWR) || $changed(VGND) || $changed(VPB) || $changed(VNB))) |-> $stable(X)
    );

endmodule