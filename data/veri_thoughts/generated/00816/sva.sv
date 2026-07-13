module Clock_Gating_Circuit_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    ///// DFF with enable behavior reflected on ENCLK /////
    // When EN was 1 last cycle, ENCLK equals last TE.
    capture_when_prev_enable_high: assert property (
        @(posedge CLK) disable iff (1'b0) (!$initstate && ($past(EN) == 1'b1)) |-> (ENCLK == $past(TE))
    );

    // When EN was 0 last cycle, ENCLK holds its previous value.
    hold_when_prev_enable_low: assert property (
        @(posedge CLK) disable iff (1'b0) (!$initstate && ($past(EN) == 1'b0)) |-> (ENCLK == $past(ENCLK))
    );

    // ENCLK can only change if EN was 1 last cycle.
    output_change_requires_prev_enable: assert property (
        @(posedge CLK) disable iff (1'b0) (!$initstate && $changed(ENCLK)) |-> $past(EN)
    );

    // If EN and TE were 1 last cycle, ENCLK must be 1 now.
    prev_enable_and_te_high_sets_output_high: assert property (
        @(posedge CLK) disable iff (1'b0) (!$initstate && $past(EN & TE)) |-> (ENCLK == 1'b1)
    );

    // If EN was 1 and TE was 0 last cycle, ENCLK must be 0 now.
    prev_enable_and_te_low_sets_output_low: assert property (
        @(posedge CLK) disable iff (1'b0) (!$initstate && $past(EN) && !$past(TE)) |-> (ENCLK == 1'b0)
    );

    // Each cycle after init, ENCLK equals either its previous value or last TE.
    output_either_prev_te_or_hold: assert property (
        @(posedge CLK) disable iff (1'b0) (!$initstate) |-> ((ENCLK == $past(ENCLK)) || (ENCLK == $past(TE)))
    );

    // If EN is 1 this cycle, ENCLK will equal TE on the next cycle.
    next_cycle_matches_te_when_enable_now: assert property (
        @(posedge CLK) disable iff (1'b0) (!$initstate && EN) |=> (ENCLK == $past(TE))
    );

    // If EN is 0 this cycle, ENCLK will hold its value on the next cycle.
    next_cycle_holds_when_enable_now_low: assert property (
        @(posedge CLK) disable iff (1'b0) (!$initstate && (EN == 1'b0)) |=> (ENCLK == $past(ENCLK))
    );

endmodule