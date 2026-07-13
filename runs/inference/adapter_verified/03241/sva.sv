module clock_gate_high_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

// ENCLK is low whenever TE is high.
    check_te_high_forces_enclk_low: assert property (
        @(posedge CLK) TE |-> (ENCLK == 1'b0)
    );

// ENCLK is high exactly when EN is high and TE is low.
    check_enclk_matches_en_when_te_low: assert property (
        @(posedge CLK) disable iff (TE) (ENCLK == EN)
    );

// With TE low, ENCLK follows EN on the next clock.
    check_en_propagates_to_enclk_when_te_low: assert property (
        @(posedge CLK) disable iff (TE) $rose(EN) |=> (ENCLK == 1'b1)
    );

// With TE low, ENCLK clears on the next clock when EN is low.
    check_enclk_clears_when_en_low: assert property (
        @(posedge CLK) disable iff (TE) $fell(EN) |=> (ENCLK == 1'b0)
    );

// With TE low, ENCLK holds its value when EN is stable.
    check_enclk_holds_when_en_stable: assert property (
        @(posedge CLK) disable iff (TE) $stable(EN) |=> (ENCLK == $past(ENCLK))
    );

endmodule
