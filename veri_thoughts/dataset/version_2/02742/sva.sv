module pulse_generator_sva (
    input logic clk,
    input logic pulse
);
    // Rising edge starts a 10-cycle HIGH pulse and then falls on the 11th cycle.
    check_pulse_width_exact_10: assert property (
        @(posedge clk) $rose(pulse) |-> (pulse [*10]) ##1 $fell(pulse)
    );

    // After a falling edge, pulse stays LOW for 101 cycles then rises.
    check_low_gap_after_fall_exact_101: assert property (
        @(posedge clk) $fell(pulse) |-> (!pulse [*101]) ##1 $rose(pulse)
    );

    // Consecutive rising edges are exactly 111 cycles apart.
    check_period_between_rises_111: assert property (
        @(posedge clk) $rose(pulse) |-> (! $rose(pulse)) [*110] ##111 $rose(pulse)
    );

    // Consecutive falling edges are exactly 111 cycles apart.
    check_period_between_falls_111: assert property (
        @(posedge clk) $fell(pulse) |-> (! $fell(pulse)) [*110] ##111 $fell(pulse)
    );

    // No additional rising edge occurs before the corresponding falling edge.
    check_no_extra_rise_before_fall: assert property (
        @(posedge clk) $rose(pulse) |-> ( ! $rose(pulse) until_with $fell(pulse) )
    );

    // No additional falling edge occurs before the next rising edge.
    check_no_extra_fall_before_rise: assert property (
        @(posedge clk) $fell(pulse) |-> ( ! $fell(pulse) until_with $rose(pulse) )
    );
endmodule