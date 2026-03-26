module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W32_1_1_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // ENCLK captures 1 when both EN and TE are high.
    check_capture_high_when_en_and_te_high: assert property (
        @(posedge CLK) ((EN === 1'b1) && (TE === 1'b1)) |=> (ENCLK === 1'b1)
    );

    // ENCLK captures 0 when EN is high and TE is low.
    check_capture_low_when_en_high_te_low: assert property (
        @(posedge CLK) ((EN === 1'b1) && (TE === 1'b0)) |=> (ENCLK === 1'b0)
    );

    // ENCLK captures 0 when EN is low and TE is high.
    check_capture_low_when_en_low_te_high: assert property (
        @(posedge CLK) ((EN === 1'b0) && (TE === 1'b1)) |=> (ENCLK === 1'b0)
    );

    // ENCLK captures 0 when both EN and TE are low.
    check_capture_low_when_en_and_te_low: assert property (
        @(posedge CLK) ((EN === 1'b0) && (TE === 1'b0)) |=> (ENCLK === 1'b0)
    );

endmodule