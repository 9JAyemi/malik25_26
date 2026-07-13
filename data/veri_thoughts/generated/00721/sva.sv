module SNPS_CLOCK_GATE_HIGH_d_ff_en_W64_0_9_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK,
    // Internal signal from RTL (bind hierarchically)
    input logic ENCLK_reg
);
    // ENCLK must equal internal register driving it.
    check_enclk_tied_to_reg: assert property (
        @(posedge CLK) ENCLK == ENCLK_reg
    );

    // When TE==0 at a clock edge, ENCLK updates next cycle to match sampled EN.
    check_update_next_cycle_match_en: assert property (
        @(posedge CLK) (TE == 1'b0) |-> ##1 (ENCLK == $past(EN))
    );

    // When TE==0 and EN==1 at a clock edge, ENCLK becomes 1 on the next clock.
    check_update_next_cycle_to_one: assert property (
        @(posedge CLK) (TE == 1'b0 && EN == 1'b1) |-> ##1 (ENCLK == 1'b1)
    );

    // When TE==0 and EN==0 at a clock edge, ENCLK becomes 0 on the next clock.
    check_update_next_cycle_to_zero: assert property (
        @(posedge CLK) (TE == 1'b0 && EN == 1'b0) |-> ##1 (ENCLK == 1'b0)
    );

    // When TE==1 at a clock edge, ENCLK holds its value to the next clock.
    check_hold_when_te_high: assert property (
        @(posedge CLK) (TE == 1'b1) |-> ##1 (ENCLK == $past(ENCLK))
    );

    // If ENCLK changes between clock edges, previous TE must have been 0.
    check_change_requires_prev_te_low: assert property (
        @(posedge CLK) $changed(ENCLK) |-> ($past(TE) == 1'b0)
    );

    // If ENCLK changes between clock edges, its new value equals previous EN.
    check_change_matches_prev_en: assert property (
        @(posedge CLK) $changed(ENCLK) |-> (ENCLK == $past(EN))
    );

    // On any clock, if previous TE was 0, current ENCLK equals previous EN.
    check_current_reflects_prev_en_when_prev_te_low: assert property (
        @(posedge CLK) ($past(TE) == 1'b0) |-> (ENCLK == $past(EN))
    );
endmodule