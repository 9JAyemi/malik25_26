module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W32_1_1_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

// ENCLK is low on the first clock after TE is high.
    check_enclk_low_after_te_rise: assert property (
        @(posedge CLK) TE |=> (ENCLK == 1'b0)
    );

// ENCLK is high on the first clock after TE is high and EN is high.
    check_enclk_high_after_te_rise_with_en: assert property (
        @(posedge CLK) (TE && EN) |=> (ENCLK == 1'b1)
    );

// ENCLK is low on the first clock after TE is high and EN is low.
    check_enclk_low_after_te_rise_without_en: assert property (
        @(posedge CLK) (TE && !EN) |=> (ENCLK == 1'b0)
    );

// ENCLK is low on the first clock after TE is low.
    check_enclk_low_after_te_fall: assert property (
        @(posedge CLK) !TE |=> (ENCLK == 1'b0)
    );

// ENCLK is high on the first clock after TE is low and EN is high.
    check_enclk_high_after_te_fall_with_en: assert property (
        @(posedge CLK) (!TE && EN) |=> (ENCLK == 1'b1)
    );

// ENCLK is low on the first clock after TE is low and EN is low.
    check_enclk_low_after_te_fall_without_en: assert property (
        @(posedge CLK) (!TE && !EN) |=> (ENCLK == 1'b0)
    );

endmodule
