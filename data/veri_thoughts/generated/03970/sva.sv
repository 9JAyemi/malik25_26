module clock_gating_assertions (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // ENCLK reflects the AND of EN and TE captured on the previous clock edge.
    check_enclk_matches_registered_and: assert property (
        @(posedge CLK) 1'b1 |=> (ENCLK == $past(EN & TE))
    );

    // When both EN and TE are high, ENCLK is high on the following cycle.
    check_enclk_sets_when_en_and_te_high: assert property (
        @(posedge CLK) (EN & TE) |=> ENCLK
    );

    // When EN is low, ENCLK is low on the following cycle.
    check_enclk_clears_when_en_low: assert property (
        @(posedge CLK) !EN |=> !ENCLK
    );

    // When TE is low, ENCLK is low on the following cycle.
    check_enclk_clears_when_te_low: assert property (
        @(posedge CLK) !TE |=> !ENCLK
    );

endmodule