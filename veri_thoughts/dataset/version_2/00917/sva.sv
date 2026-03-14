module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W17_sva (
    input logic CLK,
    input logic EN,
    input logic ENCLK,
    input logic TE
);
    // Next-cycle ENCLK equals prior TE when prior EN=1, else holds prior ENCLK.
    check_next_value_mux: assert property (
        @(posedge CLK) 1'b1 |=> (ENCLK == ($past(EN) ? $past(TE) : $past(ENCLK)))
    );

    // When EN is high, ENCLK updates next cycle to prior TE.
    check_update_on_en_high: assert property (
        @(posedge CLK) EN |=> (ENCLK == $past(TE))
    );

    // When EN is low, ENCLK holds its previous value next cycle.
    check_hold_when_en_low: assert property (
        @(posedge CLK) !EN |=> (ENCLK == $past(ENCLK))
    );

    // Any change in ENCLK between cycles requires prior EN to be high.
    check_change_requires_prev_en: assert property (
        @(posedge CLK) (ENCLK != $past(ENCLK)) |-> $past(EN)
    );

    // If ENCLK changes, the new value must equal prior TE (and prior EN must be high).
    check_change_matches_prev_te: assert property (
        @(posedge CLK) (ENCLK != $past(ENCLK)) |-> ($past(EN) && (ENCLK == $past(TE)))
    );

    // If ENCLK does not change, then either prior EN was low or prior TE equaled prior ENCLK.
    check_nochange_causes: assert property (
        @(posedge CLK) (ENCLK == $past(ENCLK)) |-> (!$past(EN) || ($past(TE) == $past(ENCLK)))
    );

    // If prior EN was high and prior TE differed from prior ENCLK, ENCLK must change.
    check_change_when_prev_te_diff: assert property (
        @(posedge CLK) ($past(EN) && ($past(TE) != $past(ENCLK))) |-> (ENCLK != $past(ENCLK))
    );
endmodule