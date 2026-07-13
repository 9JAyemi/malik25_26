module SNPS_CLOCK_GATE_HIGH_d_ff_en_W32_0_1_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // ENCLK goes high one cycle after EN&TE is exactly true.
    check_enclk_sets_when_en_and_te_high: assert property (
        @(posedge CLK) ((EN & TE) === 1'b1) |=> (ENCLK === 1'b1)
    );

    // ENCLK goes low one cycle after EN&TE is anything other than true.
    check_enclk_clears_when_en_and_te_not_high: assert property (
        @(posedge CLK) ((EN & TE) !== 1'b1) |=> (ENCLK === 1'b0)
    );

    // A low or unknown EN forces ENCLK low on the next cycle.
    check_enclk_low_when_en_not_one: assert property (
        @(posedge CLK) (EN !== 1'b1) |=> (ENCLK === 1'b0)
    );

    // A low or unknown TE forces ENCLK low on the next cycle.
    check_enclk_low_when_te_not_one: assert property (
        @(posedge CLK) (TE !== 1'b1) |=> (ENCLK === 1'b0)
    );

endmodule