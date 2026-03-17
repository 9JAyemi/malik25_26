module latch_module_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // No reset is present; ENCLK loads TE on enabled rising clocks.

    // When EN is high, ENCLK updates to the sampled TE value.
    check_load_when_enabled: assert property (
        @(posedge CLK) disable iff ($initstate)
        (EN == 1'b1) |=> (ENCLK == $past(TE))
    );

    // When EN is low, ENCLK holds its previous value.
    check_hold_when_disabled: assert property (
        @(posedge CLK) disable iff ($initstate)
        (EN == 1'b0) |=> (ENCLK == $past(ENCLK))
    );

    // A rising ENCLK must come from an enabled load of TE high.
    check_rise_requires_enabled_high_te: assert property (
        @(posedge CLK) disable iff ($initstate)
        $rose(ENCLK) |-> (($past(EN) == 1'b1) && ($past(TE) == 1'b1))
    );

    // A falling ENCLK must come from an enabled load of TE low.
    check_fall_requires_enabled_low_te: assert property (
        @(posedge CLK) disable iff ($initstate)
        $fell(ENCLK) |-> (($past(EN) == 1'b1) && ($past(TE) == 1'b0))
    );

endmodule