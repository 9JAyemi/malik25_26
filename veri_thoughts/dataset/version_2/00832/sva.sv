module TLATNTSCAX2TS_latch_module_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);
    ///// Enable-controlled register semantics /////
    // When enabled, ENCLK must equal EN on the same rising CLK edge.
    update_on_enable_matches_input: assert property (
        @(posedge CLK) TE |-> (ENCLK == EN)
    );

    // When disabled, ENCLK must not change on this rising CLK edge.
    hold_when_disabled_stable: assert property (
        @(posedge CLK) !TE |-> !$changed(ENCLK)
    );

    // Any change of ENCLK must occur only when TE is high.
    change_requires_enable: assert property (
        @(posedge CLK) $changed(ENCLK) |-> TE
    );

    // If ENCLK changes, its new value must equal EN (the source when enabled).
    change_sets_output_to_input: assert property (
        @(posedge CLK) $changed(ENCLK) |-> (ENCLK == EN)
    );

    // Full next-state function: ENCLK = (TE ? EN : previous ENCLK).
    next_state_function: assert property (
        @(posedge CLK) ENCLK == (TE ? EN : $past(ENCLK))
    );

    // On a 0->1 enable, if EN differs from previous ENCLK, ENCLK must change.
    rising_enable_diff_data_changes: assert property (
        @(posedge CLK) $rose(TE) && (EN != $past(ENCLK)) |-> $changed(ENCLK)
    );

    // On a 0->1 enable, if EN equals previous ENCLK, ENCLK must not change.
    rising_enable_same_data_no_change: assert property (
        @(posedge CLK) $rose(TE) && (EN == $past(ENCLK)) |-> !$changed(ENCLK)
    );

    // While disabled, changes on EN must not affect ENCLK at the clock edge.
    data_ignored_when_disabled: assert property (
        @(posedge CLK) (!TE && $changed(EN)) |-> !$changed(ENCLK)
    );
endmodule