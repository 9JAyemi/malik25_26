module dff_async_reset_sva (
    input logic q,
    input logic d,
    input logic clk,
    input logic reset
);
    // If reset is LOW at a clock edge, q will be 0 by the next clock.
    check_reset_low_forces_q0_next: assert property (
        @(posedge clk) !reset |-> ##1 (q == 1'b0)
    );

    // If reset is LOW at consecutive clocks, q is 0 and stable.
    check_hold_reset_keeps_q0: assert property (
        @(posedge clk) (!reset && $past(!reset)) |-> (q == 1'b0 && $stable(q))
    );

    // On the cycle reset deasserts (0->1), q is 0 before the clocked update.
    check_q_zero_on_reset_release_sample: assert property (
        @(posedge clk) $rose(reset) |-> (q == 1'b0)
    );

    // After reset deasserts, next cycle q equals d sampled at deassertion.
    check_q_captures_d_after_reset_release: assert property (
        @(posedge clk) $rose(reset) |-> ##1 (q == $past(d))
    );

    // When previous cycle was not in reset, q equals previous cycle's d.
    check_q_follows_d_when_prev_reset_high: assert property (
        @(posedge clk) disable iff (!reset) $past(reset) |-> (q == $past(d))
    );
endmodule