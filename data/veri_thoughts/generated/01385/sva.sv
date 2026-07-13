module snps_clock_gate_high_d_ff_en_w32_0_8_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);
    // When TE is 1, EN is captured to ENCLK on the next clock.
    cg_update_when_te_high: assert property (
        @(posedge CLK) TE |=> (ENCLK == $past(EN))
    );

    // When TE is 0, ENCLK holds its previous value on the next clock.
    cg_hold_when_te_low: assert property (
        @(posedge CLK) !TE |=> (ENCLK == $past(ENCLK))
    );

    // Any change in ENCLK must come from prior TE==1 and equals prior EN.
    cg_change_implies_prior_te_and_val: assert property (
        @(posedge CLK) (ENCLK != $past(ENCLK)) |-> ($past(TE) && (ENCLK == $past(EN)))
    );

    // If TE is 1 and EN equals the previous ENCLK, no change occurs next cycle.
    cg_idempotent_update_no_change: assert property (
        @(posedge CLK) (TE && (EN == $past(ENCLK))) |=> (ENCLK == $past(ENCLK,1))
    );

    // If TE is 1 and EN differs from the previous ENCLK, a change occurs next cycle.
    cg_update_causes_change_if_diff: assert property (
        @(posedge CLK) (TE && (EN != $past(ENCLK))) |=> (ENCLK != $past(ENCLK,1))
    );

    // If TE is 0 for two cycles, ENCLK two cycles later equals its value two cycles ago.
    cg_two_cycle_hold_when_te_low: assert property (
        @(posedge CLK) (!TE) ##1 (!TE) |=> (ENCLK == $past(ENCLK,2))
    );

    // If TE is 1 for two cycles, ENCLK two cycles later equals EN from one cycle ago.
    cg_two_cycle_update_when_te_high: assert property (
        @(posedge CLK) (TE) ##1 (TE) |=> (ENCLK == $past(EN,1))
    );

    // If TE is 0 for three cycles, ENCLK three cycles later equals its value three cycles ago.
    cg_three_cycle_hold_when_te_low: assert property (
        @(posedge CLK) (!TE) ##1 (!TE) ##1 (!TE) |=> (ENCLK == $past(ENCLK,3))
    );

    // If TE is 1 for three cycles, ENCLK three cycles later equals EN from one cycle ago.
    cg_three_cycle_update_when_te_high: assert property (
        @(posedge CLK) (TE) ##1 (TE) ##1 (TE) |=> (ENCLK == $past(EN,1))
    );

    // If no change occurred but prior TE was 1, then EN must have equaled the prior ENCLK.
    cg_no_change_despite_te_means_equal: assert property (
        @(posedge CLK) ((ENCLK == $past(ENCLK)) && $past(TE)) |-> ($past(EN) == $past(ENCLK))
    );
endmodule