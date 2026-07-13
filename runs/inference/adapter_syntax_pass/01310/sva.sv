module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // ENCLK is high on the first clock after EN is high.
    check_enclk_high_after_en: assert property (
        @(posedge CLK) EN |=> (ENCLK == 1'b1)
    );

    // ENCLK is low on the first clock after EN is low.
    check_enclk_low_after_en_low: assert property (
        @(posedge CLK) !EN |=> (ENCLK == 1'b0)
    );

    // ENCLK holds its value when EN is low.
    check_enclk_holds_when_en_low: assert property (
        @(posedge CLK) (!EN) |=> (ENCLK == $past(ENCLK))
    );

    // ENCLK follows TE when EN is high.
    check_enclk_follows_te_when_en_high: assert property (
        @(posedge CLK) EN |=> (ENCLK == $past(TE))
    );

endmodule