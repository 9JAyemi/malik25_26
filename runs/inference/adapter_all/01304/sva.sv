module binary_counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] count
);
    // On reset, count becomes 0 on the next cycle.
    reset_clears_next: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // When enabled and not in reset, count increments by 1 on the next cycle.
    increment_when_enabled: assert property (
        @(posedge clk) disable iff (reset) enable |=> (count == $past(count) + 4'd1)
    );

    // When not enabled and not in reset, count holds its value on the next cycle.
    hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset) !enable |=> (count == $past(count))
    );

    // Any change in count (excluding reset) implies enable was 1 in the prior cycle.
    change_requires_enable: assert property (
        @(posedge clk) disable iff (reset) (count != $past(count)) |-> $past(enable)
    );

    // If count is 0 (excluding reset), the prior cycle must have been a reset or a disabled cycle.
    zero_implies_prev_reset_or_hold: assert property (
        @(posedge clk) disable iff (reset) (count == 4'b0000) |-> ($past(reset) || !$past(enable))
    );

    // If reset is held for two consecutive cycles, count is 0 in the second cycle.
    reset_hold_keeps_zero: assert property (
        @(posedge clk) reset && $past(reset) |-> (count == 4'b0000)
    );

    // If enable is held for two consecutive cycles and count is not 0, it increments by 2.
    enable_hold_increments_by_two: assert property (
        @(posedge clk) disable iff (reset) (enable && $past(enable) && (count != 4'b0000)) |-> (count == $past(count) + 4'd2)
    );

    // If enable is held for two consecutive cycles and count is 0, it remains 0.
    enable_hold_zero_stays_zero: assert property (
        @(posedge clk) disable iff (reset) (enable && $past(enable) && (count == 4'b0000)) |-> (count == 4'b0000)
    );

    // If reset is held for two consecutive cycles and count is not 0, it becomes 0 in the second cycle.
    reset_hold_clears_nonzero: assert property (
        @(posedge clk) reset && $past(reset) && (count != 4'b0000) |-> (count == 4'b0000)
    );

    // If reset is held for two consecutive cycles and count is 0, it remains 0.
    reset_hold_zero_stays_zero: assert property (
        @(posedge clk) reset && $past(reset) && (count == 4'b0000) |-> (count == 4'b0000)
    );
endmodule