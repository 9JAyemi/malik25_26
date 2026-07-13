module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W32_0_5_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);
    // Next-state function: ENCLK_next = TE ? EN : ENCLK
    check_next_state_function: assert property (
        @(posedge CLK) 1'b1 |=> (ENCLK == ($past(TE) ? $past(EN) : $past(ENCLK)))
    );

    // When TE is high, capture EN on the next cycle
    check_capture_when_te_high: assert property (
        @(posedge CLK) TE |=> (ENCLK == $past(EN))
    );

    // When TE is low, hold ENCLK value on the next cycle
    check_hold_when_te_low: assert property (
        @(posedge CLK) !TE |=> (ENCLK == $past(ENCLK))
    );

    // Any change on ENCLK requires TE to have been high in the previous cycle
    check_change_requires_prev_te: assert property (
        @(posedge CLK) $changed(ENCLK) |-> $past(TE)
    );

    // If TE was low in the previous cycle, ENCLK must not change this cycle
    check_no_change_if_prev_te_low: assert property (
        @(posedge CLK) !$past(TE) |-> !$changed(ENCLK)
    );

    // A rising edge on ENCLK requires TE high and EN=1 in the previous cycle
    check_rise_requires_prev_te_and_en1: assert property (
        @(posedge CLK) $rose(ENCLK) |-> $past(TE && EN)
    );

    // A falling edge on ENCLK requires TE high and EN=0 in the previous cycle
    check_fall_requires_prev_te_and_en0: assert property (
        @(posedge CLK) $fell(ENCLK) |-> $past(TE && !EN)
    );

    // If TE was high in the previous cycle, ENCLK equals previous EN now
    check_current_reflects_prev_en_if_prev_te_high: assert property (
        @(posedge CLK) $past(TE) |-> (ENCLK == $past(EN))
    );

    // If TE was low in the previous cycle, ENCLK holds its previous value now
    check_current_holds_if_prev_te_low: assert property (
        @(posedge CLK) $past(!TE) |-> (ENCLK == $past(ENCLK))
    );

    // On a falling edge of TE, ENCLK at this cycle equals EN from the previous cycle
    check_te_fall_effect: assert property (
        @(posedge CLK) $fell(TE) |-> (ENCLK == $past(EN))
    );
endmodule