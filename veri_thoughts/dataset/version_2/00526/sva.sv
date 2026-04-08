module SNPS_CLOCK_GATE_HIGH_Up_counter_COUNTER_WIDTH4_sva (
    input logic CLK,
    input logic EN,
    input logic ENCLK,
    input logic TE
);

    // TE low forces the gated output low.
    check_gate_disable_forces_low: assert property (
        @(posedge CLK) !TE |-> !ENCLK
    );

    // After each clock, ENCLK matches TE ? previously sampled EN : 0.
    check_sampled_output_matches_registered_en: assert property (
        @(posedge CLK) 1'b1 |=> (ENCLK == (TE ? $past(EN) : 1'b0))
    );

    // A sampled high EN appears one cycle later when TE is high.
    check_high_en_captured_to_output: assert property (
        @(posedge CLK) EN |=> (!TE || ENCLK)
    );

    // A sampled low EN appears one cycle later as low when TE is high.
    check_low_en_captured_to_output: assert property (
        @(posedge CLK) !EN |=> (!TE || !ENCLK)
    );

endmodule