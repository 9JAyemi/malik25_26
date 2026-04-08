module power_module_sva (
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB,
    input logic HI,
    input logic LO
);

    // VPB forces HI high and LO low.
    check_vpb_branch: assert property (
        @($global_clock) VPB |-> (HI == 1'b1) && (LO == 1'b0)
    );

    // With VPB low, VPWR high and VGND low drive HI high and LO low.
    check_vpwr_branch: assert property (
        @($global_clock) (!VPB && VPWR && !VGND) |-> (HI == 1'b1) && (LO == 1'b0)
    );

    // VNB drives LO high when the HI-driving conditions are absent.
    check_vnb_branch: assert property (
        @($global_clock) (!VPB && !(VPWR && !VGND) && VNB) |-> (HI == 1'b0) && (LO == 1'b1)
    );

    // With no VPWR and asserted VGND, LO is high when higher-priority branches are absent.
    check_no_vpwr_vgnd_branch: assert property (
        @($global_clock) (!VPB && !VNB && !VPWR && VGND) |-> (HI == 1'b0) && (LO == 1'b1)
    );

    // When neither HI nor LO conditions apply, both outputs are low.
    check_default_branch: assert property (
        @($global_clock) (!VPB && !VNB && ((VPWR && VGND) || (!VPWR && !VGND))) |-> (HI == 1'b0) && (LO == 1'b0)
    );

    // HI and LO are never high at the same time.
    check_hi_lo_mutex: assert property (
        @($global_clock) !((HI == 1'b1) && (LO == 1'b1))
    );

endmodule