module nor2_pg_sva (
    input logic CLK,   // External sampling clock (RTL has no clock/reset; purely combinational)
    input logic Y,
    input logic A,
    input logic B,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    ///// Power-good mux behavior /////
    // When VPWR > VGND, Y must equal VPB.
    check_y_selects_vpb_when_pwrgood: assert property (
        @(posedge CLK) (VPWR > VGND) |-> (Y == VPB)
    );

    // When VPWR <= VGND, Y must equal VNB.
    check_y_selects_vnb_when_not_pwrgood: assert property (
        @(posedge CLK) !(VPWR > VGND) |-> (Y == VNB)
    );

    ///// Stability and dependency /////
    // If all power-related pins are stable, Y must remain stable.
    check_y_stable_when_power_pins_stable: assert property (
        @(posedge CLK) $stable(VPWR) && $stable(VGND) && $stable(VPB) && $stable(VNB) |-> $stable(Y)
    );

    // If Y changes, at least one power-related pin must have changed.
    check_y_change_implies_power_pin_change: assert property (
        @(posedge CLK) $changed(Y) |-> (!$stable(VPWR) || !$stable(VGND) || !$stable(VPB) || !$stable(VNB))
    );

    ///// Data following under fixed select /////
    // With select true and other power pins stable, Y follows VPB on VPB change.
    check_y_follows_vpb_when_pwrgood_and_vpb_changes: assert property (
        @(posedge CLK) (VPWR > VGND) && $stable(VPWR) && $stable(VGND) && $stable(VNB) && $changed(VPB)
        |-> (Y == VPB) && $changed(Y)
    );

    // With select false and other power pins stable, Y follows VNB on VNB change.
    check_y_follows_vnb_when_not_pwrgood_and_vnb_changes: assert property (
        @(posedge CLK) !(VPWR > VGND) && $stable(VPWR) && $stable(VGND) && $stable(VPB) && $changed(VNB)
        |-> (Y == VNB) && $changed(Y)
    );

endmodule