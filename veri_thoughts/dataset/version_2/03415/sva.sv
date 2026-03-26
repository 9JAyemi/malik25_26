module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W24_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // Before each rising edge, the sampled gated clock must be low.
    check_enclk_low_before_clk_rise: assert property (
        @(posedge CLK) ENCLK == 1'b0
    );

    // Before each falling edge, the sampled gated clock must equal EN & TE.
    check_enclk_matches_controls_before_clk_fall: assert property (
        @(negedge CLK) ENCLK == (EN & TE)
    );

    // A low EN or TE blocks the gated clock while CLK is high.
    check_low_control_blocks_enclk: assert property (
        @(negedge CLK) (!EN || !TE) |-> !ENCLK
    );

    // High EN and TE allow the gated clock while CLK is high.
    check_high_controls_enable_enclk: assert property (
        @(negedge CLK) (EN & TE) |-> ENCLK
    );

endmodule