module clock_gate_high_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // ENCLK is low whenever TE is asserted.
    check_te_forces_enclk_low: assert property (
        @(posedge CLK) TE |-> (ENCLK == 1'b0)
    );

    // ENCLK is high whenever EN is high and TE is low.
    check_en_high_sets_enclk: assert property (
        @(posedge CLK) disable iff (TE) EN |-> (ENCLK == 1'b1)
    );

    // ENCLK is low whenever EN is low and TE is low.
    check_en_low_clears_enclk: assert property (
        @(posedge CLK) disable iff (TE) !EN |-> (ENCLK == 1'b0)
    );

    // ENCLK can only be high when EN is high and TE is low.
    check_enclk_high_requires_en_and_not_te: assert property (
        @(posedge CLK) ENCLK |-> (EN && !TE)
    );

    // ENCLK can only be low when EN is low or TE is high.
    check_enclk_low_requires_en_low_or_te_high: assert property (
        @(posedge CLK) !ENCLK |-> (!EN || TE)
    );

endmodule