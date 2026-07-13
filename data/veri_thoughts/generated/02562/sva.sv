module slower_sva (
    input logic CLK,
    input logic SLOWCLK,
    input logic RESET,
    input logic EN_OUT
);
    // Clock: CLK posedge; Reset: RESET synchronous active-high.
    // Behavior: EN_OUT=1 iff SLOWCLK is unchanged from previous CLK; else EN_OUT=0.

    // During RESET, EN_OUT must be driven LOW.
    reset_drives_en_low: assert property (
        @(posedge CLK) RESET |-> (EN_OUT == 1'b0)
    );

    // If SLOWCLK is stable since last CLK, EN_OUT must be 1.
    en_high_on_slowclk_stable: assert property (
        @(posedge CLK) disable iff (RESET)
            ($stable(SLOWCLK) && !$past(RESET)) |-> (EN_OUT == 1'b1)
    );

    // If SLOWCLK changed since last CLK, EN_OUT must be 0.
    en_low_on_slowclk_change: assert property (
        @(posedge CLK) disable iff (RESET)
            ($changed(SLOWCLK) && !$past(RESET)) |-> (EN_OUT == 1'b0)
    );

    // EN_OUT high implies SLOWCLK was stable since last CLK.
    en_high_implies_slowclk_stable: assert property (
        @(posedge CLK) disable iff (RESET)
            (EN_OUT && !$past(RESET)) |-> $stable(SLOWCLK)
    );

    // EN_OUT low implies SLOWCLK changed since last CLK.
    en_low_implies_slowclk_changed: assert property (
        @(posedge CLK) disable iff (RESET)
            ((!EN_OUT) && !$past(RESET)) |-> $changed(SLOWCLK)
    );

    // After a SLOWCLK change, if next cycle SLOWCLK is stable then EN_OUT must be 1.
    en_recovers_high_after_change_and_stable: assert property (
        @(posedge CLK) disable iff (RESET)
            ($changed(SLOWCLK) && !$past(RESET)) ##1 ($stable(SLOWCLK) && !RESET) |-> (EN_OUT == 1'b1)
    );

    // On RESET deassertion, if SLOWCLK is 0 then EN_OUT must be 1 in that cycle.
    release_en_out_when_slowclk_zero: assert property (
        @(posedge CLK) $fell(RESET) && (SLOWCLK == 1'b0) |-> (EN_OUT == 1'b1)
    );

    // On RESET deassertion, if SLOWCLK is 1 then EN_OUT must be 0 in that cycle.
    release_en_out_when_slowclk_one: assert property (
        @(posedge CLK) $fell(RESET) && (SLOWCLK == 1'b1) |-> (EN_OUT == 1'b0)
    );

    // A falling edge on EN_OUT (1->0) occurs only when SLOWCLK changed.
    en_out_fall_only_on_slowclk_change: assert property (
        @(posedge CLK) disable iff (RESET)
            ($fell(EN_OUT) && !$past(RESET)) |-> $changed(SLOWCLK)
    );

    // A rising edge on EN_OUT (0->1) requires last cycle change and current stability of SLOWCLK.
    en_out_rise_requires_prev_change_and_now_stable: assert property (
        @(posedge CLK) disable iff (RESET)
            ($rose(EN_OUT) && !$past(RESET)) |-> (!$changed(SLOWCLK) && $past($changed(SLOWCLK)))
    );

endmodule