module sky130_fd_sc_hdll__or2_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic X
);

    // X must equal the implemented combinational expression.
    check_x_matches_rtl_expr: assert property (
        @(posedge clk)
        (X == (VPWR | (VPB & !VPWR) | (VNB & !VPB & !VPWR) | (VGND & !VNB & !VPB & !VPWR)))
    );

    // VPWR asserted drives X high.
    check_vpwr_forces_x_high: assert property (
        @(posedge clk)
        (VPWR) |-> (X)
    );

    // VPB asserted with VPWR low drives X high.
    check_vpb_forces_x_high_when_vpwr_low: assert property (
        @(posedge clk)
        (!VPWR && VPB) |-> (X)
    );

    // VNB asserted with VPWR and VPB low drives X high.
    check_vnb_forces_x_high_when_vpwr_vpb_low: assert property (
        @(posedge clk)
        (!VPWR && !VPB && VNB) |-> (X)
    );

    // VGND asserted with higher-priority pins low drives X high.
    check_vgnd_forces_x_high_when_others_low: assert property (
        @(posedge clk)
        (!VPWR && !VPB && !VNB && VGND) |-> (X)
    );

    // All power-related inputs low drives X low.
    check_all_power_low_forces_x_low: assert property (
        @(posedge clk)
        (!VPWR && !VPB && !VNB && !VGND) |-> (!X)
    );

    // Stable power pins keep X stable across samples.
    check_power_stable_keeps_x_stable: assert property (
        @(posedge clk)
        (!$initstate && $stable({VPWR, VPB, VNB, VGND})) |-> $stable(X)
    );

    // A or B changes do not affect X when power pins are stable.
    check_ab_change_does_not_affect_x: assert property (
        @(posedge clk)
        (!$initstate && $stable({VPWR, VPB, VNB, VGND}) && ($changed(A) || $changed(B))) |-> $stable(X)
    );

endmodule