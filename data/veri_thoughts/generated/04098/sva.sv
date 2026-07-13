module clock_gating_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // ENCLK must be low while CLK is low.
    check_enclk_low_on_low_clk_phase: assert property (
        @(posedge CLK) ENCLK == 1'b0
    );

    // During CLK high, ENCLK must equal EN masked by active-low TE.
    check_enclk_matches_gate_on_high_clk_phase: assert property (
        @(negedge CLK) ENCLK == (EN & ~TE)
    );

    // Outside TE-low reset, TE high must block the gated clock.
    check_te_high_blocks_enclk: assert property (
        @(negedge CLK) disable iff (!TE) ENCLK == 1'b0
    );

    // With TE low, ENCLK must follow EN during CLK high.
    check_te_low_passes_en_to_enclk: assert property (
        @(negedge CLK) !TE |-> (ENCLK == EN)
    );

    // A high ENCLK requires EN high and TE low.
    check_enclk_high_has_valid_controls: assert property (
        @(negedge CLK) ENCLK |-> (EN && !TE)
    );

endmodule