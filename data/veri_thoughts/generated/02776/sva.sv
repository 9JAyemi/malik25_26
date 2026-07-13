module clock_gate_high_register_add_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);
    // When enabled, ENCLK updates to TE on the next clock.
    update_on_enable: assert property (
        @(posedge CLK) EN |=> (ENCLK == $past(TE))
    );

    // When disabled, ENCLK holds its previous value on the next clock.
    hold_when_disabled: assert property (
        @(posedge CLK) !EN |=> (ENCLK == $past(ENCLK))
    );

    // Any change in ENCLK from one cycle to the next requires EN to have been HIGH in the prior cycle.
    change_requires_prev_enable: assert property (
        @(posedge CLK) 1'b1 |=> ((ENCLK != $past(ENCLK)) |-> $past(EN))
    );

    // If ENCLK changes, the new value must equal TE from the prior cycle.
    change_matches_prev_te: assert property (
        @(posedge CLK) 1'b1 |=> ((ENCLK != $past(ENCLK)) |-> (ENCLK == $past(TE)))
    );

    // If enabled and TE differs from current ENCLK, ENCLK must toggle on the next clock.
    enabled_differs_causes_toggle: assert property (
        @(posedge CLK) (EN && (TE != ENCLK)) |=> (ENCLK != $past(ENCLK))
    );

    // If enabled and TE equals current ENCLK, ENCLK remains unchanged on the next clock.
    enabled_same_keeps_stable: assert property (
        @(posedge CLK) (EN && (TE == ENCLK)) |=> (ENCLK == $past(ENCLK))
    );
endmodule