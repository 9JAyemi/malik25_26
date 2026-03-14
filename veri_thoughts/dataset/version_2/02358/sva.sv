module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W31_0_2_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);
    // Clock: CLK (posedge). No reset in RTL. Sequential: EN-gated register capturing TE into ENCLK.

    // ENCLK next equals TE if EN was 1, else holds previous ENCLK.
    check_functional_update_equation: assert property (
        @(posedge CLK) 1'b1 |=> (ENCLK == ($past(EN) ? $past(TE) : $past(ENCLK)))
    );

    // When EN is 1, ENCLK on the next edge equals TE from this edge.
    check_update_on_enable: assert property (
        @(posedge CLK) EN |=> (ENCLK == $past(TE))
    );

    // When EN is 0, ENCLK holds its previous value on the next edge.
    check_hold_when_disabled: assert property (
        @(posedge CLK) !EN |=> (ENCLK == $past(ENCLK))
    );

    // Any change in ENCLK across cycles implies EN was 1 in the prior cycle.
    check_change_implies_enable: assert property (
        @(posedge CLK) $changed(ENCLK) |-> $past(EN)
    );

    // If ENCLK changed, the new value equals TE from the prior cycle.
    check_changed_value_matches_prev_TE: assert property (
        @(posedge CLK) $changed(ENCLK) |-> (ENCLK == $past(TE))
    );

    // If EN is 1 and TE equals current ENCLK, no change occurs next cycle.
    check_no_change_on_enable_if_same_data: assert property (
        @(posedge CLK) (EN && (TE == ENCLK)) |=> (ENCLK == $past(ENCLK))
    );

    // If EN is 1 and TE differs from current ENCLK, a change occurs next cycle.
    check_change_on_enable_if_data_diff: assert property (
        @(posedge CLK) (EN && (TE != ENCLK)) |=> (ENCLK != $past(ENCLK))
    );

    // Each cycle, ENCLK is either the held value or the prior cycle's TE.
    check_next_value_is_prev_data_or_hold: assert property (
        @(posedge CLK) 1'b1 |=> ((ENCLK == $past(ENCLK)) || (ENCLK == $past(TE)))
    );

endmodule