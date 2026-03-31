module digital_circuit_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

// Y must match the RTL combinational equation.
    check_y_matches_rtl_equation: assert property (
        @(posedge clk)
        Y == (
            ((A1 & A2) |
             (VPWR & !VGND & !A1 & A2) |
             (!VPWR & VGND & A1 & !A2)) &
            !B1_N &
            !(VGND & VPB & VNB)
        )
    );

// A1 and A2 high must drive Y high.
    check_a1_a2_high_drive_y: assert property (
        @(posedge clk)
        (A1 & A2) |-> Y
    );

// VPWR high, VGND low, A1 low, A2 high must drive Y high.
    check_vpwr_low_vgnd_high_a1_low_a2_high_drive_y: assert property (
        @(posedge clk)
        (VPWR & !VGND & !A1 & A2) |-> Y
    );

// VPWR low, VGND high, A1 high, A2 low must drive Y high.
    check_vpwr_high_vgnd_low_a1_high_a2_low_drive_y: assert property (
        @(posedge clk)
        (!VPWR & VGND & A1 & !A2) |-> Y
    );

// B1_N low must force Y low.
    check_b1n_low_forces_y_low: assert property (
        @(posedge clk)
        !B1_N |-> !Y
    );

// VGND and VPB and VNB all high must force Y low.
    check_vgnd_vpb_vnb_high_force_y_low: assert property (
        @(posedge clk)
        (VGND & VPB & VNB) |-> !Y
    );

// Y high requires A1 and A2 to be high.
    check_y_high_requires_a1_a2: assert property (
        @(posedge clk)
        Y |-> (A1 & A2)
    );

// Y high requires B1_N to be high.
    check_y_high_requires_b1n_high: assert property (
        @(posedge clk)
        Y |-> B1_N
    );

// Y high requires not all of VGND, VPB, and VNB to be high.
    check_y_high_requires_not_all_three_high: assert property (
        @(posedge clk)
        Y |-> !(VGND & VPB & VNB)
    );

endmodule
