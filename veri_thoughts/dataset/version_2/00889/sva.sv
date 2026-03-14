module dut_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic X
);
    // X equals the logical AND of all inputs in the same cycle.
    check_x_equals_and: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge C1 or negedge C1 or
          posedge VPWR or negedge VPWR or
          posedge VGND or negedge VGND or
          posedge VPB or negedge VPB or
          posedge VNB or negedge VNB)
        X == (A1 & A2 & A3 & B1 & C1 & VPWR & VGND & VPB & VNB)
    );

    // If X is HIGH, all inputs must be HIGH in the same cycle.
    check_x_high_requires_all_ones: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge C1 or negedge C1 or
          posedge VPWR or negedge VPWR or
          posedge VGND or negedge VGND or
          posedge VPB or negedge VPB or
          posedge VNB or negedge VNB)
        X |-> (A1 & A2 & A3 & B1 & C1 & VPWR & VGND & VPB & VNB)
    );

    // If all inputs are HIGH, X must be HIGH in the same cycle.
    check_all_ones_produce_x_high: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge C1 or negedge C1 or
          posedge VPWR or negedge VPWR or
          posedge VGND or negedge VGND or
          posedge VPB or negedge VPB or
          posedge VNB or negedge VNB)
        (A1 & A2 & A3 & B1 & C1 & VPWR & VGND & VPB & VNB) |-> (X == 1'b1)
    );

    // X can only rise when all inputs are HIGH in that cycle.
    check_x_rise_requires_all_high: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge C1 or negedge C1 or
          posedge VPWR or negedge VPWR or
          posedge VGND or negedge VGND or
          posedge VPB or negedge VPB or
          posedge VNB or negedge VNB)
        $rose(X) |-> (A1 & A2 & A3 & B1 & C1 & VPWR & VGND & VPB & VNB)
    );

    // X can only fall when at least one input is LOW in that cycle.
    check_x_fall_requires_any_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge C1 or negedge C1 or
          posedge VPWR or negedge VPWR or
          posedge VGND or negedge VGND or
          posedge VPB or negedge VPB or
          posedge VNB or negedge VNB)
        $fell(X) |-> !(A1 & A2 & A3 & B1 & C1 & VPWR & VGND & VPB & VNB)
    );

    // Any input falling to 0 forces X LOW in the same cycle.
    check_any_input_fall_forces_x_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge C1 or negedge C1 or
          posedge VPWR or negedge VPWR or
          posedge VGND or negedge VGND or
          posedge VPB or negedge VPB or
          posedge VNB or negedge VNB)
        ($fell(A1) or $fell(A2) or $fell(A3) or $fell(B1) or $fell(C1) or
         $fell(VPWR) or $fell(VGND) or $fell(VPB) or $fell(VNB)) |-> (X == 1'b0)
    );

    // When the last remaining input rises to 1 (others already 1), X rises.
    check_last_input_rise_causes_x_rise: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge C1 or negedge C1 or
          posedge VPWR or negedge VPWR or
          posedge VGND or negedge VGND or
          posedge VPB or negedge VPB or
          posedge VNB or negedge VNB)
        (
            ($rose(A1)  && (A2 & A3 & B1 & C1 & VPWR & VGND & VPB & VNB)) ||
            ($rose(A2)  && (A1 & A3 & B1 & C1 & VPWR & VGND & VPB & VNB)) ||
            ($rose(A3)  && (A1 & A2 & B1 & C1 & VPWR & VGND & VPB & VNB)) ||
            ($rose(B1)  && (A1 & A2 & A3 & C1 & VPWR & VGND & VPB & VNB)) ||
            ($rose(C1)  && (A1 & A2 & A3 & B1 & VPWR & VGND & VPB & VNB)) ||
            ($rose(VPWR) && (A1 & A2 & A3 & B1 & C1 & VGND & VPB & VNB)) ||
            ($rose(VGND) && (A1 & A2 & A3 & B1 & C1 & VPWR & VPB & VNB)) ||
            ($rose(VPB)  && (A1 & A2 & A3 & B1 & C1 & VPWR & VGND & VNB)) ||
            ($rose(VNB)  && (A1 & A2 & A3 & B1 & C1 & VPWR & VGND & VPB))
        ) |-> $rose(X)
    );
endmodule