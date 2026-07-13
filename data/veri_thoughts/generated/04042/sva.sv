module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // When TE is high and EN is 1, ENCLK is 1 on the next sampled cycle.
    check_capture_one_when_te_high: assert property (
        @(posedge CLK) (TE && EN) |=> (ENCLK == 1'b1)
    );

    // When TE is high and EN is 0, ENCLK is 0 on the next sampled cycle.
    check_capture_zero_when_te_high: assert property (
        @(posedge CLK) (TE && !EN) |=> (ENCLK == 1'b0)
    );

    // When TE is low, ENCLK holds its previous sampled value.
    check_hold_when_te_low: assert property (
        @(posedge CLK) !TE |=> (ENCLK == $past(ENCLK))
    );

    // ENCLK can change only if TE was high on the previous clock edge.
    check_change_requires_prior_te: assert property (
        @(posedge CLK) 1'b1 |=> ((ENCLK == $past(ENCLK)) || $past(TE))
    );

endmodule