module fill_diode_sva (
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic fill
);

    // fill must match the RTL OR-of-ANDs equation.
    check_fill_matches_rtl_equation: assert property (
        @($global_clock) fill == ((VPWR & !VGND) | (!VPB & VNB))
    );

    // A high VPWR and low VGND must drive fill high.
    check_vpwr_high_vgnd_low_sets_fill: assert property (
        @($global_clock) (VPWR && !VGND) |-> fill
    );

    // A low VPB and high VNB must drive fill high.
    check_vpb_low_vnb_high_sets_fill: assert property (
        @($global_clock) (!VPB && VNB) |-> fill
    );

    // A low VPWR and high VGND must drive fill low.
    check_vpwr_low_vgnd_high_clears_fill: assert property (
        @($global_clock) (!VPWR && VGND) |-> !fill
    );

    // A high VPB and low VNB must drive fill low.
    check_vpb_high_vnb_low_clears_fill: assert property (
        @($global_clock) (VPB && !VNB) |-> !fill
    );

    // A high fill must come from the VPWR/VGND term.
    check_fill_high_has_vpwr_term: assert property (
        @($global_clock) fill |-> (VPWR && !VGND)
    );

    // A high fill must come from the VPB/VNB term.
    check_fill_high_has_vpb_term: assert property (
        @($global_clock) fill |-> (!VPB && VNB)
    );

    // A low fill must come from the VPWR low case.
    check_fill_low_has_vpwr_low_case: assert property (
        @($global_clock) !fill |-> (!VPWR && VGND)
    );

    // A low fill must come from the VPB high case.
    check_fill_low_has_vpb_high_case: assert property (
        @($global_clock) !fill |-> (VPB && !VNB)
    );

endmodule