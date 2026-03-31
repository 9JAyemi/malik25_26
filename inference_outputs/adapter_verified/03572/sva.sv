module ClockGating_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic RESET,
    input logic ENCLK
);

// ENCLK is 0 on the cycle after RESET is asserted.
    check_reset_clears_enclk: assert property (
        @(posedge CLK) RESET |=> (ENCLK == 1'b0)
    );

// ENCLK is 0 on the cycle after EN is deasserted.
    check_en_low_clears_enclk: assert property (
        @(posedge CLK) disable iff (RESET) !EN |=> (ENCLK == 1'b0)
    );

// ENCLK is 0 on the cycle after TE is asserted when EN is high.
    check_te_high_clears_enclk_when_en: assert property (
        @(posedge CLK) disable iff (RESET) (EN && TE) |=> (ENCLK == 1'b0)
    );

// ENCLK is 1 on the cycle after TE is deasserted when EN is high.
    check_te_low_sets_enclk_when_en: assert property (
        @(posedge CLK) disable iff (RESET) (EN && !TE) |=> (ENCLK == 1'b1)
    );

// ENCLK is 0 on the cycle after EN is asserted with TE high.
    check_en_high_te_high_clears_enclk: assert property (
        @(posedge CLK) disable iff (RESET) (EN && TE) |=> (ENCLK == 1'b0)
    );

// ENCLK is 1 on the cycle after EN is asserted with TE low.
    check_en_high_te_low_sets_enclk: assert property (
        @(posedge CLK) disable iff (RESET) (EN && !TE) |=> (ENCLK == 1'b1)
    );

endmodule
