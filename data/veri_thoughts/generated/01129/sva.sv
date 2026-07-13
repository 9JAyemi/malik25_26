module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);
    // When EN is 1 and TE is 0, ENCLK must be 1 on the next clock.
    check_enabled_sets_high_next: assert property (
        @(posedge CLK) (EN && !TE) |=> (ENCLK == 1'b1)
    );

    // When not enabled (EN==0 or TE==1), ENCLK must be 0 on the next clock.
    check_not_enabled_clears_next: assert property (
        @(posedge CLK) !(EN && !TE) |=> (ENCLK == 1'b0)
    );

    // TE overrides EN: if both EN and TE are 1, ENCLK must be 0 next clock.
    check_te_overrides_en: assert property (
        @(posedge CLK) (EN && TE) |=> (ENCLK == 1'b0)
    );

    // If enabled for two consecutive cycles, ENCLK must be 1 on the second cycle.
    check_two_cycle_enable_keeps_high: assert property (
        @(posedge CLK) (EN && !TE) ##1 (EN && !TE) |-> (ENCLK == 1'b1)
    );

    // If not enabled for two consecutive cycles, ENCLK must be 0 on the second cycle.
    check_two_cycle_not_enabled_keeps_low: assert property (
        @(posedge CLK) !(EN && !TE) ##1 !(EN && !TE) |-> (ENCLK == 1'b0)
    );

    // If TE is high for two consecutive cycles, ENCLK must be 0 on the second cycle.
    check_two_cycle_te_keeps_low: assert property (
        @(posedge CLK) TE ##1 TE |-> (ENCLK == 1'b0)
    );
endmodule