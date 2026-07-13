module fill_diode_sva (
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic fill
);

    // fill must match the implemented combinational equation.
    check_fill_equation: assert property (
        @($global_clock) fill == ((VPWR & !VGND) | (!VPB & VNB))
    );

    // VPWR high with VGND low must drive fill high.
    check_fill_high_when_vpwr_and_not_vgnd: assert property (
        @($global_clock) (VPWR && !VGND) |-> fill
    );

    // VPB low with VNB high must drive fill high.
    check_fill_high_when_not_vpb_and_vnb: assert property (
        @($global_clock) (!VPB && VNB) |-> fill
    );

    // With both VPWR/VGND terms false, fill must be low.
    check_fill_low_when_no_vpwr_term: assert property (
        @($global_clock) (!(VPWR && !VGND)) |-> !fill
    );

    // With both VPB/VNB terms false, fill must be low.
    check_fill_low_when_no_vpb_term: assert property (
        @($global_clock) (!(!VPB && VNB)) |-> !fill
    );

    // If fill is high, at least one contributing term must be true.
    check_fill_high_requires_some_term: assert property (
        @($global_clock) fill |-> ((VPWR && !VGND) || (!VPB && VNB))
    );

endmodule