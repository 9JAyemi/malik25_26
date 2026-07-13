module fill_diode_sva (
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic fill
);

    // fill must match the RTL combinational equation.
    check_fill_matches_expression: assert property (
        @($global_clock) fill == ((VPWR & !VGND) | (!VPB & VNB))
    );

    // An active VPWR/VGND term must drive fill high.
    check_fill_high_from_vpwr_path: assert property (
        @($global_clock) (VPWR & !VGND) |-> fill
    );

    // An active VPB/VNB term must drive fill high.
    check_fill_high_from_vpb_path: assert property (
        @($global_clock) (!VPB & VNB) |-> fill
    );

    // fill must be low when neither term in the RTL equation is active.
    check_fill_low_when_no_path_active: assert property (
        @($global_clock) !((VPWR & !VGND) | (!VPB & VNB)) |-> !fill
    );

endmodule