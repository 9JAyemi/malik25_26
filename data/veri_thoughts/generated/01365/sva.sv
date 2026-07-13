module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);
    // Clock: CLK (posedge). No reset in RTL.
    // Sequential logic: ENCLK registered on posedge CLK.
    // Function: ENCLK_next = (EN && TE) ? 1'b1 : 1'b0.

    // If both EN and TE are 1, next-cycle ENCLK must be 1.
    check_enclk_next_one_when_both_high: assert property (
        @(posedge CLK) (EN && TE) |-> ##1 (ENCLK == 1'b1)
    );

    // If either EN or TE is 0, next-cycle ENCLK must be 0.
    check_enclk_next_zero_when_not_both_high: assert property (
        @(posedge CLK) !(EN && TE) |-> ##1 (ENCLK == 1'b0)
    );

    // If next-cycle ENCLK is 1, then current-cycle EN and TE must both be 1.
    check_next_one_implies_both_high_now: assert property (
        @(posedge CLK) (##1 ENCLK) |-> (EN && TE)
    );

    // If next-cycle ENCLK is 0, then current-cycle not both EN and TE are 1.
    check_next_zero_implies_not_both_high_now: assert property (
        @(posedge CLK) (##1 !ENCLK) |-> !(EN && TE)
    );

    // After the first clock, ENCLK must never be X/Z (assigned to 0 or 1 every cycle).
    check_enclk_never_unknown_after_first_cycle: assert property (
        @(posedge CLK) 1'b1 |-> ##1 !$isunknown(ENCLK)
    );

endmodule