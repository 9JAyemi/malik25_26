module and4_pwr_good_sva (
    input logic X,
    input logic pwrgood_pp0_out_X,
    input logic A_N,
    input logic B,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // X equals inverted A_N & B & C & D & VPWR & VGND.
    check_x_function: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
        X == (~A_N & B & C & D & VPWR & VGND)
    );

    // pwrgood_pp0_out_X equals X & VPB & VNB.
    check_pwrgood_function: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        pwrgood_pp0_out_X == (X & VPB & VNB)
    );

    // X and pwrgood_pp0_out_X are never both HIGH.
    check_outputs_mutex: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        !(X & pwrgood_pp0_out_X)
    );

    // If X is HIGH, then B,C,D,VPWR,VGND are HIGH and A_N is LOW.
    check_x_implies_inputs: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        X |-> (~A_N & B & C & D & VPWR & VGND)
    );

    // If B,C,D,VPWR,VGND are HIGH and A_N is LOW, then X is HIGH.
    check_inputs_implies_x: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        (~A_N & B & C & D & VPWR & VGND) |-> X
    );

    // If X is LOW, then A_N is HIGH or some input is LOW.
    check_x_low_causes: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        !X |-> (A_N | ~B | ~C | ~D | ~VPWR | ~VGND)
    );

    // If VPB is LOW, pwrgood_pp0_out_X must be LOW.
    check_pwrgood_low_when_vpwr_low: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        !VPB |-> (pwrgood_pp0_out_X == 1'b0)
    );

    // If VNB is LOW, pwrgood_pp0_out_X must be LOW.
    check_pwrgood_low_when_vgnd_low: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        !VNB |-> (pwrgood_pp0_out_X == 1'b0)
    );

    // If A_N is HIGH, X must be LOW.
    check_x_low_when_a_n_high: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        A_N |-> (X == 1'b0)
    );

    // If B is LOW, X must be LOW.
    check_x_low_when_b_low: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        !B |-> (X == 1'b0)
    );

    // If C is LOW, X must be LOW.
    check_x_low_when_c_low: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        !C |-> (X == 1'b0)
    );

    // If D is LOW, X must be LOW.
    check_x_low_when_d_low: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        !D |-> (X == 1'b0)
    );

    // If VPWR is LOW, X must be LOW.
    check_x_low_when_vpwr_low: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        !VPWR |-> (X == 1'b0)
    );

    // If VGND is LOW, X must be LOW.
    check_x_low_when_vgnd_low: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        !VGND |-> (X == 1'b0)
    );

    // If all inputs are HIGH and VPB/VNB are HIGH, pwrgood_pp0_out_X is HIGH.
    check_pwrgood_high_when_all_high: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        (~A_N & B & C & D & VPWR & VGND & VPB & VNB) |-> (pwrgood_pp0_out_X == 1'b1)
    );

    // If VPB is HIGH and X is HIGH, pwrgood_pp0_out_X must be HIGH.
    check_pwrgood_follows_x_when_vpwr_high: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        (VPB & X) |->