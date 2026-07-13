module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W31_0_3_sva (
    input logic CLK,
    input logic EN,
    input logic ENCLK,
    input logic TE
);
    // Analysis: Clock=CLK (posedge), no reset. Sequential D-FF gated by TE; ENCLK is registered EN when TE=1, else holds.

    // On TE=1, ENCLK updates to EN on the next cycle.
    update_on_TE_high: assert property (
        @(posedge CLK) TE |=> (ENCLK == $past(EN))
    );

    // On TE=0, ENCLK holds its previous value on the next cycle.
    hold_when_TE_low: assert property (
        @(posedge CLK) !TE |=> (ENCLK == $past(ENCLK))
    );

    // Any change in ENCLK from last cycle implies TE was 1 in the previous cycle.
    enclk_change_requires_prev_TE: assert property (
        @(posedge CLK) (ENCLK != $past(ENCLK)) |-> $past(TE)
    );

    // If TE was 1 in the previous cycle, ENCLK equals the previous EN now.
    prev_te_high_updates_output: assert property (
        @(posedge CLK) $past(TE) |-> (ENCLK == $past(EN))
    );

    // If TE was 0 in the previous cycle, ENCLK holds its previous value now.
    prev_te_low_holds_output: assert property (
        @(posedge CLK) !$past(TE) |-> (ENCLK == $past(ENCLK))
    );

    // With TE=1, if previous EN differed from previous ENCLK, ENCLK must change next cycle.
    update_causes_change_when_input_differs: assert property (
        @(posedge CLK) TE && ($past(EN) != $past(ENCLK)) |=> (ENCLK != $past(ENCLK))
    );

    // With TE=1, if previous EN equaled previous ENCLK, ENCLK must not change next cycle.
    update_no_change_when_input_same: assert property (
        @(posedge CLK) TE && ($past(EN) == $past(ENCLK)) |=> (ENCLK == $past(ENCLK))
    );

    // One-cycle state equation: ENCLK now equals (prev TE ? prev EN : prev ENCLK).
    one_cycle_state_equation: assert property (
        @(posedge CLK) ENCLK == ($past(TE) ? $past(EN) : $past(ENCLK))
    );
endmodule