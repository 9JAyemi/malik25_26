module SNPS_CLOCK_GATE_HIGH_ShiftRegister_W7_54_sva (
    input logic CLK,
    input logic EN,
    input logic ENCLK,
    input logic TE
);
    // Clock: CLK; no reset signal present in RTL.
    // Sequential design: ENCLK and internal shift_reg/Q update on posedge CLK; no combinational feedback to ENCLK.
    // Key behavior: Updates occur only when previous (EN & ENCLK) == 1; otherwise ENCLK holds. Once ENCLK is 0, it stays 0.

    // ENCLK holds its value when previous enable (EN & ENCLK) was low.
    enclk_holds_when_prev_enable_low: assert property (
        @(posedge CLK) (!$past(EN & ENCLK)) |-> (ENCLK == $past(ENCLK))
    );

    // Any ENCLK change requires previous (EN & ENCLK) to be high.
    enclk_change_requires_prev_enable: assert property (
        @(posedge CLK) (ENCLK != $past(ENCLK)) |-> $past(EN & ENCLK)
    );

    // Once ENCLK is low, it remains low forever.
    enclk_never_rises_from_zero: assert property (
        @(posedge CLK) ($past(ENCLK) == 1'b0) |-> (ENCLK == 1'b0)
    );

    // If previous EN was low, ENCLK must hold its value.
    enclk_holds_when_prev_en_low: assert property (
        @(posedge CLK) ($past(EN) == 1'b0) |-> (ENCLK == $past(ENCLK))
    );

    // A rising edge on ENCLK can only occur when previous (EN & ENCLK) was high.
    enclk_rise_requires_prev_enable: assert property (
        @(posedge CLK) $rose(ENCLK) |-> $past(EN & ENCLK)
    );

    // A falling edge on ENCLK can only occur when previous (EN & ENCLK) was high.
    enclk_fall_requires_prev_enable: assert property (
        @(posedge CLK) $fell(ENCLK) |-> $past(EN & ENCLK)
    );

    // TE changes cannot affect ENCLK when previous enable was low.
    te_change_no_effect_when_prev_disabled: assert property (
        @(posedge CLK) ($changed(TE) && !$past(EN & ENCLK)) |-> (ENCLK == $past(ENCLK))
    );

    // TE changes cannot affect ENCLK when previous EN was low.
    te_change_no_effect_when_prev_en_low: assert property (
        @(posedge CLK) ($changed(TE) && ($past(EN) == 1'b0)) |-> (ENCLK == $past(ENCLK))
    );

    // EN changes cannot affect ENCLK when previous ENCLK was low (it must stay 0).
    en_change_no_effect_when_prev_enclk_low: assert property (
        @(posedge CLK) ($changed(EN) && ($past(ENCLK) == 1'b0)) |-> (ENCLK == 1'b0)
    );

    // If previous (EN & ENCLK) was low, ENCLK must be stable this cycle.
    enclk_stable_when_prev_not_enabled: assert property (
        @(posedge CLK) (!$past(EN & ENCLK)) |-> $stable(ENCLK)
    );
endmodule