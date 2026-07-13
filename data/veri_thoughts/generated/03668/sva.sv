module SNPS_CLOCK_GATE_HIGH_d_ff_en_W64_0_32_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK,
    input logic D,
    input logic Q,
    input logic TL
);

    // Q captures D when EN is high.
    check_q_captures_d_when_en: assert property (
        @(posedge CLK) EN |=> (Q === $past(D))
    );

    // Q holds its value when EN is low.
    check_q_holds_when_en_low: assert property (
        @(posedge CLK) !EN |=> (Q === $past(Q))
    );

    // TL captures the prior Q value when TE is high.
    check_tl_captures_q_when_te: assert property (
        @(posedge CLK) TE |=> (TL === $past(Q))
    );

    // TL holds its value when TE is low.
    check_tl_holds_when_te_low: assert property (
        @(posedge CLK) !TE |=> (TL === $past(TL))
    );

    // TE forces ENCLK high.
    check_enclk_high_when_te: assert property (
        @(posedge CLK) TE |=> (ENCLK == 1'b1)
    );

    // EN drives ENCLK high when TE is low.
    check_enclk_high_when_en_only: assert property (
        @(posedge CLK) (!TE && EN) |=> (ENCLK == 1'b1)
    );

    // With both controls low, ENCLK is driven low.
    check_enclk_low_when_disabled: assert property (
        @(posedge CLK) (!TE && !EN) |=> (ENCLK == 1'b0)
    );

endmodule