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

    // X must mirror pwrgood_pp0_out_X (buffer behavior).
    check_X_mirrors_pwrgood: assert property (
        @(posedge A_N or posedge B or posedge C or posedge D or posedge VPWR or posedge VGND or posedge VPB or posedge VNB or posedge X or posedge pwrgood_pp0_out_X)
        X == pwrgood_pp0_out_X
    );

    // X equals ~A_N & B & C & D & VPWR & VGND.
    check_X_functional_equivalence: assert property (
        @(posedge A_N or posedge B or posedge C or posedge D or posedge VPWR or posedge VGND or posedge VPB or posedge VNB or posedge X or posedge pwrgood_pp0_out_X)
        X == ((~A_N) & B & C & D & VPWR & VGND)
    );

    // pwrgood_pp0_out_X equals ~A_N & B & C & D & VPWR & VGND.
    check_pwrgood_functional_equivalence: assert property (
        @(posedge A_N or posedge B or posedge C or posedge D or posedge VPWR or posedge VGND or posedge VPB or posedge VNB or posedge X or posedge pwrgood_pp0_out_X)
        pwrgood_pp0_out_X == ((~A_N) & B & C & D & VPWR & VGND)
    );

    // If VPWR is LOW, outputs must be LOW.
    check_outputs_zero_when_VPWR_low: assert property (
        @(posedge A_N or posedge B or posedge C or posedge D or posedge VPWR or posedge VGND or posedge VPB or posedge VNB or posedge X or posedge pwrgood_pp0_out_X)
        (VPWR == 1'b0) |-> (X == 1'b0 && pwrgood_pp0_out_X == 1'b0)
    );

    // If VGND is LOW, outputs must be LOW.
    check_outputs_zero_when_VGND_low: assert property (
        @(posedge A_N or posedge B or posedge C or posedge D or posedge VPWR or posedge VGND or posedge VPB or posedge VNB or posedge X or posedge pwrgood_pp0_out_X)
        (VGND == 1'b0) |-> (X == 1'b0 && pwrgood_pp0_out_X == 1'b0)
    );

    // If A_N is HIGH, outputs must be LOW.
    check_outputs_zero_when_A_N_high: assert property (
        @(posedge A_N or posedge B or posedge C or posedge D or posedge VPWR or posedge VGND or posedge VPB or posedge VNB or posedge X or posedge pwrgood_pp0_out_X)
        (A_N == 1'b1) |-> (X == 1'b0 && pwrgood_pp0_out_X == 1'b0)
    );

    // If B is LOW, outputs must be LOW.
    check_outputs_zero_when_B_low: assert property (
        @(posedge A_N or posedge B or posedge C or posedge D or posedge VPWR or posedge VGND or posedge VPB or posedge VNB or posedge X or posedge pwrgood_pp0_out_X)
        (B == 1'b0) |-> (X == 1'b0 && pwrgood_pp0_out_X == 1'b0)
    );

    // If C is LOW, outputs must be LOW.
    check_outputs_zero_when_C_low: assert property (
        @(posedge A_N or posedge B or posedge C or posedge D or posedge VPWR or posedge VGND or posedge VPB or posedge VNB or posedge X or posedge pwrgood_pp0_out_X)
        (C == 1'b0) |-> (X == 1'b0 && pwrgood_pp0_out_X == 1'b0)
    );

    // If D is LOW, outputs must be LOW.
    check_outputs_zero_when_D_low: assert property (
        @(posedge A_N or posedge B or posedge C or posedge D or posedge VPWR or posedge VGND or posedge VPB or posedge VNB or posedge X or posedge pwrgood_pp0_out_X)
        (D == 1'b0) |-> (X == 1'b0 && pwrgood_pp0_out_X == 1'b0)
    );

    // If all inputs and power-good are true, outputs must be HIGH.
    check_outputs_high_when_all_true: assert property (
        @(posedge A_N or posedge B or posedge C or posedge D or posedge VPWR or posedge VGND or posedge VPB or posedge VNB or posedge X or posedge pwrgood_pp0_out_X)
        ((~A_N) & B & C & D & VPWR & VGND) |-> (X == 1'b1 && pwrgood_pp0_out_X == 1'b1)
    );

    // When power rails are HIGH, X equals ~A_N & B & C & D.
    check_X_equiv_when_power_good: assert property (
        @(posedge A_N or posedge B or posedge C or posedge D or posedge VPWR or posedge VGND or posedge VPB or posedge VNB or posedge X or posedge pwrgood_pp0_out_X)
        ((VPWR == 1'b1) && (VGND == 1'b1)) |-> (X == ((~A_N) & B & C & D))
    );

    // VPB changes alone must not affect outputs.
    check_outputs_independent_of_VPB: assert property (
        @(posedge A_N or posedge B or posedge C or posedge D or posedge VPWR or posedge VGND or posedge VPB or posedge VNB or posedge X or posedge pwrgood_pp0_out_X)
        (((VPB != $past(VPB))) && $stable(A_N) && $stable(B) && $stable(C) && $stable(D) && $stable(VPWR) && $stable(VGND))
        |-> ($stable(X) && $stable(pwrgood_pp0_out_X))
    );

    // VNB changes alone must not affect outputs.
    check_outputs_independent_of_VNB: assert property (
        @(posedge A_N or posedge B or posedge C or posedge D or posedge VPWR or posedge VGND or posedge VPB or posedge VNB or posedge X or posedge pwrgood_pp0_out_X)
        (((VNB != $past(VNB))) && $stable(A_N) && $stable(B) && $stable(C) && $stable(D) && $stable(VPWR) && $stable(VGND))
        |-> ($stable(X) && $stable(pwrgood_pp0_out_X))
    );

endmodule