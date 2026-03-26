module clock_gate_assertions (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // TE high captures a high EN into ENCLK.
    check_capture_high: assert property (
        @(posedge CLK) (TE && EN) |=> ENCLK
    );

    // TE high captures a low EN into ENCLK.
    check_capture_low: assert property (
        @(posedge CLK) (TE && !EN) |=> !ENCLK
    );

    // TE low holds ENCLK high.
    check_hold_high_when_te_low: assert property (
        @(posedge CLK) (!TE && ENCLK) |=> ENCLK
    );

    // TE low holds ENCLK low.
    check_hold_low_when_te_low: assert property (
        @(posedge CLK) (!TE && !ENCLK) |=> !ENCLK
    );

    // With TE high, ENCLK matches the prior EN value.
    check_enabled_update_matches_en: assert property (
        @(posedge CLK) TE |=> (ENCLK == $past(EN))
    );

    // With TE low, ENCLK keeps its prior value.
    check_disabled_hold_matches_previous: assert property (
        @(posedge CLK) !TE |=> (ENCLK == $past(ENCLK))
    );

endmodule