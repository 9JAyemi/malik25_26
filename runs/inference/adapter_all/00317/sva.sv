module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W32_1_1_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);
    // ENCLK equals EN delayed by one cycle.
    check_enclk_one_cycle_delay: assert property (
        @(posedge CLK) disable iff ($initstate) ENCLK == $past(EN)
    );

    // TE high causes ENCLK to equal EN on the next cycle.
    check_te_high_captures_en: assert property (
        @(posedge CLK) disable iff ($initstate) TE |=> (ENCLK == $past(EN))
    );

    // TE low causes ENCLK to hold its previous value on the next cycle.
    check_te_low_holds_enclk: assert property (
        @(posedge CLK) disable iff ($initstate) !TE |=> (ENCLK == $past(ENCLK))
    );

    // If EN and TE are stable, ENCLK is stable on the next cycle.
    check_stable_inputs_keep_enclk_stable: assert property (
        @(posedge CLK) disable iff ($initstate) $stable(EN) && $stable(TE) |=> $stable(ENCLK)
    );

    // If EN and TE differ, ENCLK changes on the next cycle.
    check_mismatched_inputs_change_enclk: assert property (
        @(posedge CLK) disable iff ($initstate) (EN ^ TE) |=> (ENCLK != $past(ENCLK))
    );

    // If EN and TE are equal, ENCLK equals EN on the next cycle.
    check_equal_inputs_pass_en: assert property (
        @(posedge CLK) disable iff ($initstate) !(EN ^ TE) |=> (ENCLK == $past(EN))
    );

    // If EN and TE differ, ENCLK equals TE on the next cycle.
    check_mismatched_inputs_pass_te: assert property (
        @(posedge CLK) disable iff ($initstate) (EN ^ TE) |=> (ENCLK == $past(TE))
    );

    // If EN and TE are equal, ENCLK equals EN on the next cycle.
    check_equal_inputs_pass_en: assert property (
        @(posedge CLK) disable iff ($initstate) !(EN ^ TE) |=> (ENCLK == $past(EN))
    );

    // If EN and TE differ, ENCLK equals TE on the next cycle.
    check_mismatched_inputs_pass_te: assert property (
        @(posedge CLK) disable iff ($initstate) (EN ^ TE) |=> (ENCLK == $past(TE))
    );

    // If EN and TE are equal, ENCLK equals EN on the next cycle.
    check_equal_inputs_pass_en: assert property (
        @(posedge CLK) disable iff ($initstate) !(EN ^ TE) |=> (ENCLK == $past(EN))
    );

    // If EN and TE differ, ENCLK equals TE on the next cycle.
    check_mismatched_inputs_pass_te: assert property (
        @(posedge CLK) disable iff ($initstate) (EN ^ TE) |=> (ENCLK == $past(TE))
    );
endmodule