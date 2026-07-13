module ClockGating_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic RESET,
    input logic ENCLK
);

    // ENCLK is low whenever reset is asserted.
    check_reset_clears_enclk: assert property (
        @(posedge CLK) RESET |-> (ENCLK == 1'b0)
    );

    // ENCLK is low on the first clock after reset deasserts.
    check_reset_release_clears_enclk: assert property (
        @(posedge CLK) disable iff (RESET) $fell(RESET) |-> (ENCLK == 1'b0)
    );

    // ENCLK is low when EN is low.
    check_en_low_clears_enclk: assert property (
        @(posedge CLK) disable iff (RESET) (!EN) |-> (ENCLK == 1'b0)
    );

    // ENCLK is low when EN and TE are both high.
    check_te_high_clears_enclk: assert property (
        @(posedge CLK) disable iff (RESET) (EN && TE) |-> (ENCLK == 1'b0)
    );

    // ENCLK is high when EN is high and TE is low.
    check_te_low_sets_enclk: assert property (
        @(posedge CLK) disable iff (RESET) (EN && !TE) |-> (ENCLK == 1'b1)
    );

    // ENCLK is high on the first clock after EN and TE are high.
    check_te_high_sets_enclk: assert property (
        @(posedge CLK) disable iff (RESET) ($past(RESET) && $past(EN) && $past(TE)) |-> (ENCLK == 1'b1)
    );

endmodule