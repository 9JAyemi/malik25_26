module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic RST,
    input logic ENCLK
);

    // Synchronous reset drives ENCLK low on the next clock.
    check_reset_clears_enclk: assert property (
        @(posedge CLK) RST |=> (ENCLK == 1'b0)
    );

    // Reset has priority over TE when both are asserted.
    check_reset_overrides_te: assert property (
        @(posedge CLK) (RST && TE) |=> (ENCLK == 1'b0)
    );

    // When TE is high, EN=1 is captured into ENCLK.
    check_te_captures_one: assert property (
        @(posedge CLK) disable iff (RST) (TE && EN) |=> (ENCLK == 1'b1)
    );

    // When TE is high, EN=0 is captured into ENCLK.
    check_te_captures_zero: assert property (
        @(posedge CLK) disable iff (RST) (TE && !EN) |=> (ENCLK == 1'b0)
    );

    // When TE is low, a high ENCLK value is held.
    check_hold_high_when_te_low: assert property (
        @(posedge CLK) disable iff (RST) (!TE && ENCLK) |=> (ENCLK == 1'b1)
    );

    // When TE is low, a low ENCLK value is held.
    check_hold_low_when_te_low: assert property (
        @(posedge CLK) disable iff (RST) (!TE && !ENCLK) |=> (ENCLK == 1'b0)
    );

endmodule