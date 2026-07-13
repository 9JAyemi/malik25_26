module clock_gate_d_ff_en_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // EN low forces ENCLK low.
    check_en_low_forces_enclk_low: assert property (
        @(posedge CLK) !EN |-> !ENCLK
    );

    // ENCLK can only be high when EN is high.
    check_enclk_high_requires_en: assert property (
        @(posedge CLK) ENCLK |-> EN
    );

    // When TE is high, the next-cycle ENCLK reflects the captured EN value.
    check_capture_when_te: assert property (
        @(posedge CLK) TE |=> (ENCLK == (EN ? $past(EN) : 1'b0))
    );

    // With EN high and TE low, ENCLK holds if EN stays high.
    check_hold_when_te_low_and_enabled: assert property (
        @(posedge CLK) (EN && !TE) |=> (!EN || (ENCLK == $past(ENCLK)))
    );

endmodule