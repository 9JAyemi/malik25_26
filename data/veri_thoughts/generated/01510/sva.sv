module clock_gate_high_d_ff_en_w32_0_19_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);
    // Asynchronous clear: EN rising forces ENCLK low immediately.
    check_async_clear_enclk_on_en: assert property (
        @(posedge EN) ENCLK == 1'b0
    );

    // On every CLK edge, ENCLK is driven low by the sequential logic.
    check_enclk_low_on_every_clk: assert property (
        @(posedge CLK) ENCLK == 1'b0
    );

    // During reset (EN high) at a CLK edge, ENCLK must be low.
    check_sync_clear_when_en_high: assert property (
        @(posedge CLK) EN |-> (ENCLK == 1'b0)
    );

    // Out of reset (EN low), ENCLK remains low on CLK edges.
    check_enclk_low_out_of_reset: assert property (
        @(posedge CLK) disable iff (EN) (ENCLK == 1'b0)
    );

    // Out of reset, ENCLK can never rise on a CLK edge.
    check_enclk_never_rises_out_of_reset: assert property (
        @(posedge CLK) disable iff (EN) !$rose(ENCLK)
    );

    // ENCLK is known (not X/Z) on each CLK edge.
    check_enclk_known_on_clk: assert property (
        @(posedge CLK) !$isunknown(ENCLK)
    );
endmodule