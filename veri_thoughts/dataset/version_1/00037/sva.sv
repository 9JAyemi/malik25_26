module latch_sva (
    input logic E,
    input logic SE,
    input logic CK,
    input logic ECK
);

    // When SE is high and E is high, ECK is set on the next clock.
    latch_set_when_se_and_e_high: assert property (
        @(posedge CK) (SE && E) |=> (ECK == 1'b1)
    );

    // When SE is high and E is low, ECK is cleared on the next clock.
    latch_clear_when_se_high_and_e_low: assert property (
        @(posedge CK) (SE && !E) |=> (ECK == 1'b0)
    );

    // When SE is low, ECK holds its value across clocks.
    latch_hold_when_se_low: assert property (
        @(posedge CK) (!SE) |=> $stable(ECK)
    );

endmodule

module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // When TE is high and EN is high, ENCLK is set on the next clock.
    clock_gate_set_when_te_and_en_high: assert property (
        @(posedge CLK) (TE && EN) |=> (ENCLK == 1'b1)
    );

    // When TE is high and EN is low, ENCLK is cleared on the next clock.
    clock_gate_clear_when_te_high_and_en_low: assert property (
        @(posedge CLK) (TE && !EN) |=> (ENCLK == 1'b0)
    );

    // When TE is low, ENCLK holds its value across clocks.
    clock_gate_hold_when_te_low: assert property (
        @(posedge CLK) (!TE) |=> $stable(ENCLK)
    );

endmodule