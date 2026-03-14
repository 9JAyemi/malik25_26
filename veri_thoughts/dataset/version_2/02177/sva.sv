module power_good_checker_sva (
    input logic CLK,
    input logic A,
    input logic SLEEP_B,
    input logic VPWR,
    input logic KAGND,
    input logic VPB,
    input logic VNB,
    input logic X
);
    ///// Functional definition /////
    // X equals A && SLEEP_B && VPWR && KAGND.
    check_x_definition: assert property (
        @(posedge CLK) X == (A && SLEEP_B && VPWR && KAGND)
    );

    ///// Necessary conditions for X HIGH /////
    // If X is HIGH then A, SLEEP_B, VPWR, and KAGND must be HIGH.
    check_x_implies_all_high: assert property (
        @(posedge CLK) (X == 1'b1) |-> (A && SLEEP_B && VPWR && KAGND)
    );

    ///// Sufficient conditions for X HIGH /////
    // If A, SLEEP_B, VPWR, and KAGND are all HIGH then X must be HIGH.
    check_all_high_implies_x_high: assert property (
        @(posedge CLK) (A && SLEEP_B && VPWR && KAGND) |-> (X == 1'b1)
    );

    ///// Low input forces X LOW /////
    // If VPWR is LOW then X must be LOW.
    check_x_low_when_vpwr_low: assert property (
        @(posedge CLK) (VPWR == 1'b0) |-> (X == 1'b0)
    );
    // If KAGND is LOW then X must be LOW.
    check_x_low_when_kagnd_low: assert property (
        @(posedge CLK) (KAGND == 1'b0) |-> (X == 1'b0)
    );
    // If A is LOW then X must be LOW.
    check_x_low_when_a_low: assert property (
        @(posedge CLK) (A == 1'b0) |-> (X == 1'b0)
    );
    // If SLEEP_B is LOW then X must be LOW.
    check_x_low_when_sleepb_low: assert property (
        @(posedge CLK) (SLEEP_B == 1'b0) |-> (X == 1'b0)
    );

    ///// Stability and independence /////
    // If A, SLEEP_B, VPWR, and KAGND are stable, X must be stable.
    check_x_stable_when_used_inputs_stable: assert property (
        @(posedge CLK) ($stable(A) && $stable(SLEEP_B) && $stable(VPWR) && $stable(KAGND)) |-> $stable(X)
    );
    // X is unaffected by VPB changes when used inputs are stable.
    check_x_unchanged_on_vpb_toggle: assert property (
        @(posedge CLK) ($changed(VPB) && $stable(A) && $stable(SLEEP_B) && $stable(VPWR) && $stable(KAGND)) |-> $stable(X)
    );
    // X is unaffected by VNB changes when used inputs are stable.
    check_x_unchanged_on_vnb_toggle: assert property (
        @(posedge CLK) ($changed(VNB) && $stable(A) && $stable(SLEEP_B) && $stable(VPWR) && $stable(KAGND)) |-> $stable(X)
    );
endmodule