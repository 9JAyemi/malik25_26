module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic RST,
    input logic ENCLK
);
    // Clock: CLK (posedge). Reset: RST (synchronous, active-high). Sequential flop with enable/transparent load.

    // Reset drives ENCLK low on the next cycle.
    reset_clears_next: assert property (
        @(posedge CLK) RST |=> (ENCLK == 1'b0)
    );

    // With TE high, ENCLK loads EN on the next cycle.
    load_on_te: assert property (
        @(posedge CLK) disable iff (RST) TE |=> (ENCLK == $past(EN))
    );

    // With TE low, ENCLK holds its previous value.
    hold_when_te_low: assert property (
        @(posedge CLK) disable iff (RST) !TE |=> (ENCLK == $past(ENCLK))
    );

    // If TE and EN differ, ENCLK changes on the next cycle.
    change_when_te_and_en_mismatch: assert property (
        @(posedge CLK) disable iff (RST) (TE && (EN != ENCLK)) |=> (ENCLK != $past(ENCLK))
    );

    // If TE and EN match, ENCLK does not change on the next cycle.
    no_change_when_te_and_en_match: assert property (
        @(posedge CLK) disable iff (RST) (TE && (EN == ENCLK)) |=> (ENCLK == $past(ENCLK))
    );

    // Any ENCLK change must be caused by prior RST or TE.
    change_requires_prev_reset_or_te: assert property (
        @(posedge CLK) disable iff (RST) $changed(ENCLK) |-> ($past(RST) || $past(TE))
    );

    // If TE is high and EN equals current ENCLK, ENCLK holds.
    hold_when_te_high_and_en_matches: assert property (
        @(posedge CLK) disable iff (RST) (TE && (EN == ENCLK)) |=> (ENCLK == $past(ENCLK))
    );

    // If TE is high and EN differs from current ENCLK, ENCLK changes.
    change_when_te_high_and_en_differs: assert property (
        @(posedge CLK) disable iff (RST) (TE && (EN != ENCLK)) |=> (ENCLK != $past(ENCLK))
    );

    // If TE is low and EN differs from current ENCLK, ENCLK changes.
    change_when_te_low_and_en_differs: assert property (
        @(posedge CLK) disable iff (RST) (!TE && (EN != ENCLK)) |=> (ENCLK != $past(ENCLK))
    );

    // If TE is low and EN equals current ENCLK, ENCLK holds.
    hold_when_te_low_and_en_matches: assert property (
        @(posedge CLK) disable iff (RST) (!TE && (EN == ENCLK)) |=> (ENCLK == $past(ENCLK))
    );

endmodule