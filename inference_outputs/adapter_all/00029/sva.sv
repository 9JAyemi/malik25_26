module binary_counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] q
);
    // Reset drives q to zero on the next clock.
    reset_clears_q_next: assert property (
        @(posedge clk) reset |=> (q == 4'b0000)
    );

    // When enabled, q increments by 1 on the next clock.
    increment_when_enabled: assert property (
        @(posedge clk) disable iff (reset) enable |=> (q == $past(q) + 4'd1)
    );

    // When not enabled, q holds its value on the next clock.
    hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset) !enable |=> (q == $past(q))
    );

    // If enabled and q is 4'hF, it wraps to 4'h0 on the next clock.
    wrap_on_max: assert property (
        @(posedge clk) disable iff (reset) (enable && (q == 4'hF)) |=> (q == 4'h0)
    );

    // Any change in q must be caused by reset or enable in the prior cycle.
    change_requires_reset_or_enable: assert property (
        @(posedge clk) disable iff (reset) (q != $past(q)) |-> ($past(reset) || $past(enable))
    );

    // If reset and enable are both high, reset has priority and q becomes 0 on the next clock.
    reset_priority_over_enable: assert property (
        @(posedge clk) (reset && enable) |=> (q == 4'h0)
    );

    // If reset is held high across consecutive clocks, q remains 0.
    reset_held_keeps_q_zero: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (q == 4'h0)
    );

    // If enable is held high across consecutive clocks and q is not 4'hF, it increments by 1.
    enable_held_increments: assert property (
        @(posedge clk) disable iff (reset) (enable && $past(enable) && ($past(q) != 4'hF)) |-> (q == $past(q) + 4'd1)
    );

    // If enable is held high across consecutive clocks and q is 4'hF, it wraps to 4'h0.
    enable_held_wraps: assert property (
        @(posedge clk) disable iff (reset) (enable && $past(enable) && ($past(q) == 4'hF)) |-> (q == 4'h0)
    );

    // If reset is high and enable is low, q remains 0 on the next clock.
    reset_high_disable_low_keeps_zero: assert property (
        @(posedge clk) (reset && !enable) |=> (q == 4'h0)
    );
endmodule