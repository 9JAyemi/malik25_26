module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W13_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // CLK is the sampled clock; EN acts as an active-low asynchronous clear.
    
    // If EN is low at a sampled clock edge, the gated output must be low.
    check_en_low_clears_output: assert property (
        @(posedge CLK) disable iff ($initstate)
        !EN |-> !ENCLK
    );

    // A sampled low EN keeps the gated output low through the next sampled clock edge.
    check_en_low_holds_output_low_next_cycle: assert property (
        @(posedge CLK) disable iff ($initstate)
        !EN |=> !ENCLK
    );

    // The first sampled cycle after EN rises still sees the gated output low.
    check_en_rise_seen_before_clocked_set: assert property (
        @(posedge CLK) disable iff ($initstate)
        $rose(EN) |-> !ENCLK
    );

    // A sampled fall of EN must coincide with a low gated output.
    check_en_fall_clears_output: assert property (
        @(posedge CLK) disable iff ($initstate)
        $fell(EN) |-> !ENCLK
    );

    // A high gated output must come from EN having been high on the prior clock edge.
    check_enclk_high_requires_prev_en_high: assert property (
        @(posedge CLK) disable iff ($initstate)
        ENCLK |-> $past(EN)
    );

    // A high gated output cannot coexist with EN low at a sampled clock edge.
    check_enclk_high_requires_en_high_now: assert property (
        @(posedge CLK) disable iff ($initstate)
        ENCLK |-> EN
    );

endmodule