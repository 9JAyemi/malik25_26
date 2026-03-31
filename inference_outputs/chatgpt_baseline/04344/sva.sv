module digital_circuit_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // Y must match the implemented combinational equation.
    check_y_matches_equation: assert property (
        @($global_clock)
        Y == ((((A1 & A2) |
                (VPWR & !VGND & !A1 & A2) |
                (!VPWR & VGND & A1 & !A2))) &
              !B1_N &
              !(VGND & VPB & VNB))
    );

    // B1_N high always forces Y low.
    check_b1_n_blocks_output: assert property (
        @($global_clock)
        B1_N |-> !Y
    );

    // The VGND/VPB/VNB inhibit term always forces Y low.
    check_inhibit_term_blocks_output: assert property (
        @($global_clock)
        (VGND & VPB & VNB) |-> !Y
    );

    // A high Y requires B1_N to be low.
    check_y_requires_b1_n_low: assert property (
        @($global_clock)
        Y |-> !B1_N
    );

    // A high Y requires the inhibit term to be inactive.
    check_y_requires_inhibit_inactive: assert property (
        @($global_clock)
        Y |-> !(VGND & VPB & VNB)
    );

    // The A1&A2 product term drives Y when gating allows it.
    check_a1_a2_term_drives_y: assert property (
        @($global_clock)
        (A1 & A2 & !B1_N & !(VGND & VPB & VNB)) |-> Y
    );

    // The VPWR-assisted product term drives Y when gating allows it.
    check_vpwr_assist_term_drives_y: assert property (
        @($global_clock)
        (VPWR & !VGND & !A1 & A2 & !B1_N & !(VGND & VPB & VNB)) |-> Y
    );

    // The VGND-assisted product term drives Y when gating allows it.
    check_vgnd_assist_term_drives_y: assert property (
        @($global_clock)
        (!VPWR & VGND & A1 & !A2 & !B1_N & !(VGND & VPB & VNB)) |-> Y
    );

    // If no product term is active, Y must be low.
    check_no_active_product_forces_low: assert property (
        @($global_clock)
        (!(A1 & A2) &
         !(VPWR & !VGND & !A1 & A2) &
         !(!VPWR & VGND & A1 & !A2)) |-> !Y
    );

    // If Y is high while A1 is low, it must be via the VPWR-assisted path.
    check_y_with_a1_low_identifies_path: assert property (
        @($global_clock)
        (Y & !A1) |-> (A2 & VPWR & !VGND)
    );

    // If Y is high while A2 is low, it must be via the VGND-assisted path.
    check_y_with_a2_low_identifies_path: assert property (
        @($global_clock)
        (Y & !A2) |-> (A1 & !VPWR & VGND)
    );

endmodule