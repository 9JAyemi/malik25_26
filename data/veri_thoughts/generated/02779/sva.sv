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
    // X equals the combinational expression in the RTL.
    check_function_equivalence: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge VPWR or negedge VPWR or
          posedge VGND or negedge VGND or
          posedge VPB or negedge VPB or
          posedge VNB or negedge VNB)
        X == (A1 & ~A2 & ~A3 & ~B1 & ~B2 & ~VPWR & ~VGND & ~VPB & ~VNB)
    );

    // If X is HIGH, all input conditions required by the RTL must hold.
    check_x_high_implies_inputs_match: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge VPWR or negedge VPWR or
          posedge VGND or negedge VGND or
          posedge VPB or negedge VPB or
          posedge VNB or negedge VNB)
        X |-> (A1 && !A2 && !A3 && !B1 && !B2 && !VPWR && !VGND && !VPB && !VNB)
    );

    // If all input conditions match the RTL expression, X must be HIGH.
    check_inputs_match_implies_x_high: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge VPWR or negedge VPWR or
          posedge VGND or negedge VGND or
          posedge VPB or negedge VPB or
          posedge VNB or negedge VNB)
        (A1 && !A2 && !A3 && !B1 && !B2 && !VPWR && !VGND && !VPB && !VNB) |-> X
    );

    // A1 LOW forces X LOW.
    check_a1_low_forces_x_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge VPWR or negedge VPWR or
          posedge VGND or negedge VGND or
          posedge VPB or negedge VPB or
          posedge VNB or negedge VNB)
        (!A1) |-> (!X)
    );

    // A2 HIGH forces X LOW.
    check_a2_high_forces_x_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge VPWR or negedge VPWR or
          posedge VGND or negedge VGND or
          posedge VPB or negedge VPB or
          posedge VNB or negedge VNB)
        (A2) |-> (!X)
    );

    // A3 HIGH forces X LOW.
    check_a3_high_forces_x_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge VPWR or negedge VPWR or
          posedge VGND or negedge VGND or
          posedge VPB or negedge VPB or
          posedge VNB or negedge VNB)
        (A3) |-> (!X)
    );

    // B1 HIGH forces X LOW.
    check_b1_high_forces_x_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge VPWR or negedge VPWR or
          posedge VGND or negedge VGND or
          posedge VPB or negedge VPB or
          posedge VNB or negedge VNB)
        (B1) |-> (!X)
    );

    // B2 HIGH forces X LOW.
    check_b2_high_forces_x_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge VPWR or negedge VPWR or
          posedge VGND or negedge VGND or
          posedge VPB or negedge VPB or
          posedge VNB or negedge VNB)
        (B2) |-> (!X)
    );

    // VPWR HIGH forces X LOW (due to ~VPWR term).
    check_vpwr_high_forces_x_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge VPWR or negedge VPWR or
          posedge VGND or negedge VGND or
          posedge VPB or negedge VPB or
          posedge VNB or negedge VNB)
        (VPWR) |-> (!X)
    );

    // VGND HIGH forces X LOW (due to ~VGND term).
    check_vgnd_high_forces_x_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge VPWR or negedge VPWR or
          posedge VGND or negedge VGND or
          posedge VPB or negedge VPB or
          posedge VNB or negedge VNB)
        (VGND) |-> (!X)
    );

    // VPB HIGH forces X LOW (due to ~VPB term).
    check_vpb_high_forces_x_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge VPWR or negedge VPWR or
          posedge VGND or negedge VGND or
          posedge VPB or negedge VPB or
          posedge VNB or negedge VNB)
        (VPB) |-> (!X)
    );

    // VNB HIGH forces X LOW (due to ~VNB term).
    check_vnb_high_forces_x_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge VPWR or negedge VPWR or
          posedge VGND or negedge VGND or
          posedge VPB or negedge VPB or
          posedge VNB or negedge VNB)
        (VNB) |-> (!X)
    );
endmodule