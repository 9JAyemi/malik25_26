module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // When CLK is low, the gated output must be low.
    check_low_phase_output_low: assert property (
        @(posedge CLK) ENCLK == 1'b0
    );

    // During CLK high, the gated output must equal EN & ~TE.
    check_high_phase_function: assert property (
        @(negedge CLK) ENCLK == (EN & ~TE)
    );

    // If enable is low, the gated output must be low during CLK high.
    check_enable_low_blocks_output: assert property (
        @(negedge CLK) !EN |-> (ENCLK == 1'b0)
    );

    // If test enable is high, the gated output must be low during CLK high.
    check_test_enable_blocks_output: assert property (
        @(negedge CLK) TE |-> (ENCLK == 1'b0)
    );

    // If enabled and not in test mode, the gated output must be high during CLK high.
    check_enabled_non_test_passes_clock: assert property (
        @(negedge CLK) (EN && !TE) |-> (ENCLK == 1'b1)
    );

endmodule