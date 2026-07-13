module data_power_module_sva (
    input logic A,
    input logic X,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

    ///// Power gating on output /////
    // When VPWR is LOW, X must be LOW.
    check_x_low_when_vpwr_low: assert property (
        @(posedge VPB) (VPWR == 1'b0) |-> (X == 1'b0)
    );

    ///// Output function /////
    // X equals (current VPWR) AND (A from previous VPB edge).
    check_x_eq_vpwr_and_past_a: assert property (
        @(posedge VPB) X == (VPWR & $past(A))
    );

    // If VPWR is HIGH, X equals A from previous VPB edge.
    check_power_high_implies_x_eq_past_a: assert property (
        @(posedge VPB) (VPWR == 1'b1) |-> (X == $past(A))
    );

    // If A was LOW at the previous VPB edge, X must be LOW now.
    check_past_a_low_implies_x_low: assert property (
        @(posedge VPB) ($past(A) == 1'b0) |-> (X == 1'b0)
    );

    // X can only be HIGH when both VPWR and previous A are HIGH.
    check_x_high_requires_power_and_past_a_high: assert property (
        @(posedge VPB) (X == 1'b1) |-> ((VPWR == 1'b1) && ($past(A) == 1'b1))
    );

endmodule