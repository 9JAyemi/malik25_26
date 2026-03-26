module my_module_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic Y
);

    // Y must match the implemented OR-of-products expression.
    check_y_matches_logic: assert property (
        @($global_clock)
        Y == ((A1 & A2) | (B1 & C1 & D1) | (VPWR & !VGND) | (VPB & !VNB))
    );

    // A1 and A2 high must make Y high.
    check_a1_a2_term_drives_y: assert property (
        @($global_clock)
        (A1 & A2) |-> Y
    );

    // B1, C1, and D1 high must make Y high.
    check_b1_c1_d1_term_drives_y: assert property (
        @($global_clock)
        (B1 & C1 & D1) |-> Y
    );

    // VPWR high with VGND low must make Y high.
    check_vpwr_vgnd_term_drives_y: assert property (
        @($global_clock)
        (VPWR & !VGND) |-> Y
    );

    // VPB high with VNB low must make Y high.
    check_vpb_vnb_term_drives_y: assert property (
        @($global_clock)
        (VPB & !VNB) |-> Y
    );

    // If all implemented terms are low, Y must be low.
    check_no_active_term_means_y_low: assert property (
        @($global_clock)
        !((A1 & A2) | (B1 & C1 & D1) | (VPWR & !VGND) | (VPB & !VNB)) |-> !Y
    );

endmodule