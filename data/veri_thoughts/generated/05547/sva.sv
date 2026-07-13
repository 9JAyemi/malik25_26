module SNPS_CLOCK_GATE_HIGH_RegisterMult_W24_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // ENCLK is low whenever CLK is sampled low.
    check_enclk_low_on_clk_low_phase: assert property (
        @(posedge CLK) ENCLK == 1'b0
    );

    // With both controls high, ENCLK is high while CLK is high.
    check_enclk_high_when_en_and_te_high: assert property (
        @(negedge CLK) ((EN == 1'b1) && (TE == 1'b1)) |-> (ENCLK == 1'b1)
    );

    // ENCLK is low while CLK is high if EN is low.
    check_enclk_low_when_en_low: assert property (
        @(negedge CLK) (EN == 1'b0) |-> (ENCLK == 1'b0)
    );

    // ENCLK is low while CLK is high if TE is low.
    check_enclk_low_when_te_low: assert property (
        @(negedge CLK) (TE == 1'b0) |-> (ENCLK == 1'b0)
    );

    // ENCLK can only be high while CLK is high when both controls are high.
    check_enclk_high_requires_en_and_te: assert property (
        @(negedge CLK) (ENCLK == 1'b1) |-> ((EN == 1'b1) && (TE == 1'b1))
    );

endmodule