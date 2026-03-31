module ClockGating_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic RESET,
    input logic ENCLK
);
    // During reset, ENCLK must be 0.
    reset_forces_enclk_low: assert property (
        @(posedge CLK) RESET |-> (ENCLK == 1'b0)
    );

    // If EN is 0, ENCLK must be 0 on the next cycle.
    en_low_clears_enclk_next: assert property (
        @(posedge CLK) disable iff (RESET) (!EN) |=> (ENCLK == 1'b0)
    );

    // If EN is 1 and TE is 1, ENCLK must be 0 on the next cycle.
    en_high_te_high_clears_enclk_next: assert property (
        @(posedge CLK) disable iff (RESET) (EN && TE) |=> (ENCLK == 1'b0)
    );

    // If EN is 1 and TE is 0, ENCLK must be 1 on the next cycle.
    en_high_te_low_sets_enclk_next: assert property (
        @(posedge CLK) disable iff (RESET) (EN && !TE) |=> (ENCLK == 1'b1)
    );

    // If EN and TE are stable and EN is 1, ENCLK must change on the next cycle.
    en_high_te_stable_changes_enclk_next: assert property (
        @(posedge CLK) disable iff (RESET) (EN && TE && $stable(EN) && $stable(TE)) |=> $changed(ENCLK)
    );

    // If EN and TE are stable and EN is 0, ENCLK must not change on the next cycle.
    en_low_te_stable_no_change_next: assert property (
        @(posedge CLK) disable iff (RESET) (!EN && $stable(EN) && $stable(TE)) |=> !$changed(ENCLK)
    );

    // If EN is 1 and TE is 0, ENCLK must be 1 on the same cycle.
    en_high_te_low_sets_enclk_now: assert property (
        @(posedge CLK) disable iff (RESET) (EN && !TE) |-> (ENCLK == 1'b1)
    );

    // If EN is 1 and TE is 1, ENCLK must be 0 on the same cycle.
    en_high_te_high_clears_enclk_now: assert property (
        @(posedge CLK) disable iff (RESET) (EN && TE) |-> (ENCLK == 1'b0)
    );

    // If EN is 0, ENCLK must be 0 on the same cycle.
    en_low_clears_enclk_now: assert property (
        @(posedge CLK) disable iff (RESET) (!EN) |-> (ENCLK == 1'b0)
    );

    // If EN is 1 and TE is 0, ENCLK must change on the next cycle.
    en_high_te_low_changes_enclk_next: assert property (
        @(posedge CLK) disable iff (RESET) (EN && !TE) |=> $changed(ENCLK)
    );
endmodule