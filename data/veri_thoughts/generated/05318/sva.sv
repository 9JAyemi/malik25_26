module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // If EN is low, the gated clock output is low on the next rising edge.
    check_disable_clears_output: assert property (
        @(posedge CLK) disable iff (1'b0) (!EN) |=> (ENCLK == 1'b0)
    );

    // If EN and TE are high, the gated clock output is high on the next rising edge.
    check_test_enable_sets_output: assert property (
        @(posedge CLK) disable iff (1'b0) (EN && TE) |=> (ENCLK == 1'b1)
    );

    // If EN is high and TE is low, capturing CLK at the rising edge still drives output high.
    check_clk_capture_sets_output: assert property (
        @(posedge CLK) disable iff (1'b0) (EN && !TE) |=> (ENCLK == 1'b1)
    );

    // ENCLK always reflects the EN value sampled on the previous rising edge.
    check_output_tracks_previous_en: assert property (
        @(posedge CLK) disable iff (1'b0) 1'b1 |=> (ENCLK == $past(EN))
    );

endmodule