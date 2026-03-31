module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic RST,
    input logic ENCLK
);

    // ENCLK is low on the first clock after reset is released.
    check_reset_release_clears_enclk: assert property (
        @(posedge CLK) disable iff (RST)
        $fell(RST) |-> (ENCLK == 1'b0)
    );

    // ENCLK holds its value when reset is held high.
    check_reset_holds_enclk: assert property (
        @(posedge CLK) disable iff (RST)
        $past(RST) |-> (ENCLK == $past(ENCLK))
    );

    // ENCLK is cleared when the prior cycle had reset and TE low.
    check_clear_when_reset_and_te_low: assert property (
        @(posedge CLK) disable iff (RST)
        $past(RST && !TE) |-> (ENCLK == 1'b0)
    );

    // ENCLK captures EN when the prior cycle had reset low and TE high.
    check_capture_en_when_te_high: assert property (
        @(posedge CLK) disable iff (RST)
        $past(!RST && TE) |-> (ENCLK == $past(EN))
    );

    // ENCLK holds its value when the prior cycle had reset low and TE low.
    check_hold_when_te_low: assert property (
        @(posedge CLK) disable iff (RST)
        $past(!RST && !TE) |-> (ENCLK == $past(ENCLK))
    );

endmodule