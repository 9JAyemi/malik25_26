module dffc_6_sva (
    input logic clk,
    input logic reset,
    input logic [5:0] d,
    input logic [5:0] q
);
    // q must be 0 whenever reset is asserted (active-low).
    check_reset_forces_zero: assert property (
        @(posedge clk) (reset == 1'b0) |-> (q == 6'b0)
    );

    // On a falling edge of reset, q is 0 at this clock sample.
    check_zero_on_reset_fall_sample: assert property (
        @(posedge clk) $fell(reset) |-> (q == 6'b0)
    );

    // On a rising edge of reset, q is 0 at this clock sample.
    check_zero_on_reset_rise_sample: assert property (
        @(posedge clk) $rose(reset) |-> (q == 6'b0)
    );

    // With reset high in consecutive cycles, q equals last cycle's d.
    check_capture_d_when_reset_high: assert property (
        @(posedge clk) disable iff (!reset) $past(reset) |-> (q == $past(d))
    );

    // First clock after reset release captures the d value from the release cycle.
    check_first_cycle_after_release_captures_d: assert property (
        @(posedge clk) disable iff (!reset) $rose(reset) |-> ##1 (q == $past(d))
    );

    // If d held constant over the last two cycles (no reset), q does not change.
    check_stability_when_d_unchanged: assert property (
        @(posedge clk) disable iff (!reset)
            ($past(reset,2) && $past(reset) && ($past(d) == $past(d,2))) |-> (q == $past(q))
    );

    // If q changes (no reset), the change was caused by a change in d in the prior cycle.
    check_q_change_requires_d_change: assert property (
        @(posedge clk) disable iff (!reset)
            ($past(reset,2) && $past(reset) && (q != $past(q))) |-> ($past(d) != $past(d,2))
    );

    // When reset is high, next cycle's q equals this cycle's d (if reset stays high).
    check_next_cycle_captures_d_when_reset_high: assert property (
        @(posedge clk) disable iff (!reset) reset |-> ##1 (q == $past(d))
    );
endmodule