module clock_gate_high_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // TE clears the stored enable value by the next clock sample.
    check_te_forces_low_next: assert property (
        @(posedge CLK) disable iff ($initstate) TE |=> !ENCLK
    );

    // With TE low, EN=0 is captured as a 0.
    check_en_low_captures_low: assert property (
        @(posedge CLK) disable iff ($initstate) (!TE && !EN) |=> !ENCLK
    );

    // A sampled high output must come from a prior enabled capture.
    check_high_requires_prev_enabled_capture: assert property (
        @(posedge CLK) disable iff ($initstate) ENCLK |-> $past(!TE && EN)
    );

    // If TE was high or EN was low on the prior clock, the output is low now.
    check_prev_blocking_condition_gives_low: assert property (
        @(posedge CLK) disable iff ($initstate) $past(TE || !EN) |-> !ENCLK
    );

endmodule