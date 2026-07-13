module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

// ENCLK is high on the next clock when TE was high and EN was high.
    check_enclk_set_on_te_high: assert property (
        @(posedge CLK) TE |=> (ENCLK == 1'b1)
    );

// ENCLK is low on the next clock when TE was high and EN was low.
    check_enclk_clear_on_te_high_en_low: assert property (
        @(posedge CLK) (TE && !EN) |=> (ENCLK == 1'b0)
    );

// ENCLK holds its value on the next clock when TE was low.
    check_enclk_holds_when_te_low: assert property (
        @(posedge CLK) !TE |=> $stable(ENCLK)
    );

endmodule
