module clk_divider_sva (
    input logic sysclk,
    input logic slowclk
);
    // Clock: sysclk; Reset: none; Sequential divider toggling slowclk every 51 sysclk cycles (period 102).

    // After any slowclk edge, it must be stable for the next 50 cycles.
    slowclk_no_early_toggle_50: assert property (
        @(posedge sysclk) $changed(slowclk) |-> (!$changed(slowclk))[*50]
    );

    // After any slowclk edge, it must toggle again exactly 51 cycles later.
    slowclk_toggle_at_51: assert property (
        @(posedge sysclk) $changed(slowclk) |-> ##51 $changed(slowclk)
    );

    // A rising edge is followed by a falling edge 51 cycles later (no earlier changes).
    slowclk_rise_then_fall_51: assert property (
        @(posedge sysclk) $rose(slowclk) |-> (!$changed(slowclk))[*50] ##1 $fell(slowclk)
    );

    // A falling edge is followed by a rising edge 51 cycles later (no earlier changes).
    slowclk_fall_then_rise_51: assert property (
        @(posedge sysclk) $fell(slowclk) |-> (!$changed(slowclk))[*50] ##1 $rose(slowclk)
    );

    // Rising edge repeats every 102 cycles (full period).
    slowclk_rise_period_102: assert property (
        @(posedge sysclk) $rose(slowclk) |-> ##102 $rose(slowclk)
    );

    // Falling edge repeats every 102 cycles (full period).
    slowclk_fall_period_102: assert property (
        @(posedge sysclk) $fell(slowclk) |-> ##102 $fell(slowclk)
    );

    // No back-to-back toggles on consecutive sysclk cycles.
    slowclk_no_adjacent_toggles: assert property (
        @(posedge sysclk) $changed(slowclk) |-> ##1 !$changed(slowclk)
    );

endmodule