module SNPS_CLOCK_GATE_HIGH_d_ff_en_W32_0_6_sva (
    input logic CLK,
    input logic EN,
    input logic ENCLK,
    input logic TE
);

    // Clock: CLK; reset: none.
    // ENCLK is a latch output that is transparent while CLK is high.

    // In test mode, ENCLK is forced high by the end of the CLK-high phase.
    check_test_mode_forces_high: assert property (
        @(negedge CLK) TE |-> (ENCLK == 1'b1)
    );

    // In normal mode, ENCLK matches EN by the end of the CLK-high phase.
    check_normal_mode_passes_enable: assert property (
        @(negedge CLK) !TE |-> (ENCLK == EN)
    );

    // At the end of the transparent phase, ENCLK equals the implemented latch function.
    check_latch_function: assert property (
        @(negedge CLK) ENCLK == (TE ? 1'b1 : EN)
    );

endmodule