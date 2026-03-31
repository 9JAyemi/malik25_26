module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

// ENCLK is 0 on the first clock after EN is 0.
    check_enclk_zero_after_en_low: assert property (
        @(posedge CLK) !EN |=> (ENCLK == 1'b0)
    );

// ENCLK holds its value when EN is 0.
    check_enclk_holds_when_en_low: assert property (
        @(posedge CLK) !EN |=> $stable(ENCLK)
    );

// ENCLK is 0 when EN is 0.
    check_enclk_zero_when_en_low: assert property (
        @(posedge CLK) !EN |-> (ENCLK == 1'b0)
    );

// ENCLK is 1 when EN is 1 and TE is 1.
    check_enclk_one_when_en_and_te_high: assert property (
        @(posedge CLK) (EN && TE) |=> (ENCLK == 1'b1)
    );

// ENCLK is 0 when EN is 1 and TE is 0.
    check_enclk_zero_when_en_and_te_low: assert property (
        @(posedge CLK) (EN && !TE) |=> (ENCLK == 1'b0)
    );

// ENCLK is 1 when EN is 1 and TE was 1 on the previous clock.
    check_enclk_one_when_prev_te_high: assert property (
        @(posedge CLK) (EN && $past(TE)) |=> (ENCLK == 1'b1)
    );

// ENCLK is 0 when EN is 1 and TE was 0 on the previous clock.
    check_enclk_zero_when_prev_te_low: assert property (
        @(posedge CLK) (EN && !$past(TE)) |=> (ENCLK == 1'b0)
    );

endmodule
