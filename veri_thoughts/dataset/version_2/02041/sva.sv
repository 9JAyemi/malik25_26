module voltage_level_shifter_sva (
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic VPB_OUT,
    input logic VNB_OUT,
    input logic VPWR_OUT,
    input logic VGND_OUT
);
    // No clock/reset in DUT; combinational only. Sample on any edge of DUT inputs.

    // VPWR_OUT must equal VPWR.
    check_vpwr_passthrough: assert property (
        @(posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        (VPWR_OUT == VPWR)
    );

    // VGND_OUT must equal VGND.
    check_vgnd_passthrough: assert property (
        @(posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        (VGND_OUT == VGND)
    );

    // When VPB is 1, VPB_OUT must equal VPWR.
    check_vpb_selects_vpwr_when_one: assert property (
        @(posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        (VPB == 1'b1) |-> (VPB_OUT == VPWR)
    );

    // When VPB is 0, VPB_OUT must equal VGND.
    check_vpb_selects_vgnd_when_zero: assert property (
        @(posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        (VPB == 1'b0) |-> (VPB_OUT == VGND)
    );

    // When VNB is 1, VNB_OUT must equal VPWR.
    check_vnb_selects_vpwr_when_one: assert property (
        @(posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        (VNB == 1'b1) |-> (VNB_OUT == VPWR)
    );

    // When VNB is 0, VNB_OUT must equal VGND.
    check_vnb_selects_vgnd_when_zero: assert property (
        @(posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        (VNB == 1'b0) |-> (VNB_OUT == VGND)
    );

    // VPB_OUT must be either VPWR or VGND.
    check_vpb_out_is_supply: assert property (
        @(posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        (VPB_OUT == VPWR) || (VPB_OUT == VGND)
    );

    // VNB_OUT must be either VPWR or VGND.
    check_vnb_out_is_supply: assert property (
        @(posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        (VNB_OUT == VPWR) || (VNB_OUT == VGND)
    );

    // If supplies are equal, all outputs must equal that value.
    check_equal_supplies_make_all_outs_equal: assert property (
        @(posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        (VPWR == VGND) |-> ((VPWR_OUT == VGND_OUT) && (VPB_OUT == VPWR) && (VNB_OUT == VPWR) && (VGND_OUT == VPWR))
    );

    // If VPB and VNB are equal, VPB_OUT and VNB_OUT must be equal.
    check_equal_controls_equal_body_outs: assert property (
        @(posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        (VPB == VNB) |-> (VPB_OUT == VNB_OUT)
    );

    // If VPB!=VNB and supplies differ, VPB_OUT and VNB_OUT must differ.
    check_unequal_controls_and_supplies_give_diff_outs: assert property (
        @(posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        ((VPB != VNB) && (VPWR != VGND)) |-> (VPB_OUT != VNB_OUT)
    );

endmodule