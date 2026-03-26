module sky130_fd_sc_hd__lpflow_bleeder_sva (
    input logic SHORT,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // VPWR always matches the implemented continuous assignment.
    check_vpwr_matches_assign: assert property (
        @($global_clock) VPWR === (SHORT ? VGND : (VPB - VNB))
    );

    // When SHORT is high, VPWR follows VGND.
    check_short_selects_vgnd: assert property (
        @($global_clock) (SHORT === 1'b1) |-> (VPWR === VGND)
    );

    // When SHORT is low, VPWR follows VPB - VNB.
    check_short_deasserted_selects_difference: assert property (
        @($global_clock) (SHORT === 1'b0) |-> (VPWR === (VPB - VNB))
    );

endmodule