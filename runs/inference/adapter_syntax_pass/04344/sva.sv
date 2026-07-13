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

    // Y matches the RTL combinational equation.
    check_y_matches_rtl_equation: assert property (
        @($global_clock)
        Y == (
            ((A1 & A2) |
             (VPWR & !VGND & !A1 & A2) |
             (!VPWR & VGND & A1 & !A2)) &
            !B1_N &
            !(VGND & VPB & VNB)
        )
    );

    // B1_N high forces Y low.
    check_b1n_high_forces_y_low: assert property (
        @($global_clock)
        B1_N |-> !Y
    );

    // VGND and VPB high together force Y low.
    check_vgnd_vpb_high_forces_y_low: assert property (
        @($global_clock)
        (VGND & VPB) |-> !Y
    );

    // VGND and VNB high together force Y low.
    check_vgnd_vnb_high_forces_y_low: assert property (
        @($global_clock)
        (VGND & VNB) |-> !Y
    );

    // A1 and A2 high force Y high.
    check_a1_a2_high_force_y_high: assert property (
        @($global_clock)
        (A1 & A2) |-> Y
    );

    // VPWR high, VGND low, A1 low, and A2 high force Y high.
    check_vpwr_high_vgnd_low_a1_low_a2_high_force_y_high: assert property (
        @($global_clock)
        (VPWR & !VGND & !A1 & A2) |-> Y
    );

    // VPWR low, VGND high, A1 high, and A2 low force Y high.
    check_vpwr_low_vgnd_high_a1_high_a2_low_force_y_high: assert property (
        @($global_clock)
        (!VPWR & VGND & A1 & !A2) |-> Y
    );

    // A1 low and A2 high force Y low.
    check_a1_low_a2_high_force_y_low: assert property (
        @($global_clock)
        (!A1 & A2) |-> !Y
    );

    // A1 high and A2 low force Y low.
    check_a1_high_a2_low_force_y_low: assert property (
        @($global_clock)
        (A1 & !A2) |-> !Y
    );

    // VPWR low, VGND low, and A1 low force Y low.
    check_vpwr_low_vgnd_low_a1_low_force_y_low: assert property (
        @($global_clock)
        (!VPWR & !VGND & !A1) |-> !Y
    );

    // VPWR low, VGND low, and A2 high force Y low.
    check_vpwr_low_vgnd_low_a2_high_force_y_low: assert property (
        @($global_clock)
        (!VPWR & !VGND & A2) |-> !Y
    );

endmodule