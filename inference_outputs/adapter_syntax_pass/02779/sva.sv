module sky130_fd_sc_lp__a32o_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic X
);

    // X must match the RTL AND equation.
    check_x_matches_rtl_equation: assert property (
        @($global_clock)
        X == (A1 & ~A2 & ~A3 & ~B1 & ~B2 & ~VPWR & ~VGND & ~VPB & ~VNB)
    );

    // A1 high forces X high.
    check_a1_high_forces_x_high: assert property (
        @($global_clock)
        A1 |-> X
    );

    // A2 high forces X low.
    check_a2_high_forces_x_low: assert property (
        @($global_clock)
        A2 |-> !X
    );

    // A3 high forces X low.
    check_a3_high_forces_x_low: assert property (
        @($global_clock)
        A3 |-> !X
    );

    // B1 high forces X low.
    check_b1_high_forces_x_low: assert property (
        @($global_clock)
        B1 |-> !X
    );

    // B2 high forces X low.
    check_b2_high_forces_x_low: assert property (
        @($global_clock)
        B2 |-> !X
    );

    // VPWR high forces X low.
    check_vpwr_high_forces_x_low: assert property (
        @($global_clock)
        VPWR |-> !X
    );

    // VGND high forces X low.
    check_vgnd_high_forces_x_low: assert property (
        @($global_clock)
        VGND |-> !X
    );

    // VPB high forces X low.
    check_vpb_high_forces_x_low: assert property (
        @($global_clock)
        VPB |-> !X
    );

    // VNB high forces X low.
    check_vnb_high_forces_x_low: assert property (
        @($global_clock)
        VNB |-> !X
    );

endmodule