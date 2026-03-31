module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W32_1_1_sva (
    input logic CLK,
    input logic EN,
    input logic ENCLK,
    input logic TE
);

    // An enabled edge captures EN into ENCLK by the next sampled cycle.
    check_capture_when_enabled: assert property (
        @(posedge CLK) TE |=> (ENCLK === $past(EN))
    );

    // A disabled edge leaves ENCLK unchanged by the next sampled cycle.
    check_hold_when_disabled: assert property (
        @(posedge CLK) !TE |=> (ENCLK === $past(ENCLK))
    );

    // ENCLK becomes 1 after an enabled edge with EN high.
    check_capture_high_when_enabled: assert property (
        @(posedge CLK) (TE && EN) |=> (ENCLK === 1'b1)
    );

    // ENCLK becomes 0 after an enabled edge with EN low.
    check_capture_low_when_enabled: assert property (
        @(posedge CLK) (TE && !EN) |=> (ENCLK === 1'b0)
    );

endmodule