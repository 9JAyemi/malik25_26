module clock_gate_4bit_up_counter_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // TE has priority and drives ENCLK low on the next cycle.
    check_te_forces_enclk_low: assert property (
        @(posedge CLK) disable iff ($initstate)
        TE |=> (ENCLK == 1'b0)
    );

    // A low-to-high EN transition with TE low raises ENCLK for the next cycle.
    check_en_rise_sets_enclk: assert property (
        @(posedge CLK) disable iff ($initstate)
        (!TE && EN && !$past(EN)) |=> (ENCLK == 1'b1)
    );

    // A sustained high EN with TE low does not generate another ENCLK pulse.
    check_en_high_no_repeat_pulse: assert property (
        @(posedge CLK) disable iff ($initstate)
        (!TE && EN && $past(EN)) |=> (ENCLK == 1'b0)
    );

    // A low EN with TE low keeps ENCLK low on the next cycle.
    check_en_low_clears_enclk: assert property (
        @(posedge CLK) disable iff ($initstate)
        (!TE && !EN) |=> (ENCLK == 1'b0)
    );

    // ENCLK can only be high if TE was low and EN was high on the prior clock.
    check_enclk_requires_prev_en_and_te_low: assert property (
        @(posedge CLK) disable iff ($initstate)
        ENCLK |-> (!$past(TE) && $past(EN))
    );

    // ENCLK is a single-cycle pulse once the sampled history is established.
    check_enclk_is_single_cycle_pulse: assert property (
        @(posedge CLK) disable iff ($initstate)
        ENCLK |=> (ENCLK == 1'b0)
    );

endmodule