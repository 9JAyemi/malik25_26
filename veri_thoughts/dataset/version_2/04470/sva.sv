module power_check_sva (
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic power_ok
);

    // power_ok must always match the VPWR/VPB AND function.
    check_power_ok_matches_and: assert property (
        @($global_clock) power_ok == (VPWR && VPB)
    );

    // power_ok high requires VPWR to be high.
    check_power_ok_implies_vpwr: assert property (
        @($global_clock) power_ok |-> VPWR
    );

    // power_ok high requires VPB to be high.
    check_power_ok_implies_vpb: assert property (
        @($global_clock) power_ok |-> VPB
    );

    // A low VPWR must force power_ok low.
    check_low_vpwr_forces_power_not_ok: assert property (
        @($global_clock) !VPWR |-> !power_ok
    );

    // A low VPB must force power_ok low.
    check_low_vpb_forces_power_not_ok: assert property (
        @($global_clock) !VPB |-> !power_ok
    );

    // Changing VGND alone must not change power_ok.
    check_vgnd_unused: assert property (
        @($global_clock)
        !$initstate && $changed(VGND) && $stable(VPWR) && $stable(VPB) && $stable(VNB)
        |-> $stable(power_ok)
    );

    // Changing VNB alone must not change power_ok.
    check_vnb_unused: assert property (
        @($global_clock)
        !$initstate && $changed(VNB) && $stable(VPWR) && $stable(VPB) && $stable(VGND)
        |-> $stable(power_ok)
    );

endmodule