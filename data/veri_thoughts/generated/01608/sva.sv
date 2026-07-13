module clock_gate_register_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic reset,
    input logic ENCLK
);
    ///// Reset behavior /////
    // While reset is asserted (active-high), ENCLK must be 0.
    reset_clears_output: assert property (
        @(posedge CLK) reset |-> (ENCLK == 1'b0)
    );

    ///// Test enable gating /////
    // TE low forces ENCLK low.
    te_low_forces_zero: assert property (
        @(posedge CLK) disable iff (reset) (TE == 1'b0) |-> (ENCLK == 1'b0)
    );
    // ENCLK high implies TE is high (gated path).
    enclk_high_requires_te: assert property (
        @(posedge CLK) disable iff (reset) (ENCLK == 1'b1) |-> (TE == 1'b1)
    );
    // Any rise of ENCLK requires TE high in that cycle.
    enclk_rise_requires_te: assert property (
        @(posedge CLK) disable iff (reset) $rose(ENCLK) |-> (TE == 1'b1)
    );
endmodule