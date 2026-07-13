module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // EN high with TE low drives ENCLK high on the next cycle.
    check_en_and_not_te_sets_enclk: assert property (
        @(posedge CLK) (EN && !TE) |=> ENCLK
    );

    // EN low drives ENCLK low on the next cycle.
    check_en_low_clears_enclk: assert property (
        @(posedge CLK) !EN |=> !ENCLK
    );

    // TE high drives ENCLK low on the next cycle.
    check_te_high_clears_enclk: assert property (
        @(posedge CLK) TE |=> !ENCLK
    );

    // After the first clock, ENCLK matches the previous cycle's EN && !TE.
    check_enclk_matches_previous_controls: assert property (
        @(posedge CLK) $past(1'b1) |-> (ENCLK == $past(EN && !TE))
    );

    // A high ENCLK must come from EN high and TE low in the previous cycle.
    check_high_enclk_has_valid_previous_controls: assert property (
        @(posedge CLK) ($past(1'b1) && ENCLK) |-> $past(EN && !TE)
    );

endmodule