module counter_3bit_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [2:0] count
);
    // Reset low forces count to zero at the sampling edge.
    reset_forces_zero: assert property (
        @(posedge clk) (!reset) |-> (count == 3'd0)
    );

    // On the first clock after reset deasserts, count is still zero.
    zero_on_reset_release: assert property (
        @(posedge clk) ($past(!reset) && reset) |-> (count == 3'd0)
    );

    // With enable LOW, count holds its previous value (when out of reset).
    hold_when_enable_low: assert property (
        @(posedge clk) disable iff (!reset) ($past(reset) && !enable) |-> (count == $past(count))
    );

    // With enable HIGH, count increments by 1 modulo 8 (when out of reset).
    increment_when_enable_high: assert property (
        @(posedge clk) disable iff (!reset) ($past(reset) && enable) |-> (count == (($past(count) == 3'd7) ? 3'd0 : ($past(count) + 3'd1)))
    );

    // When previous count was 7 and enable HIGH, wrap to 0.
    wrap_on_max_value: assert property (
        @(posedge clk) disable iff (!reset) ($past(reset) && ($past(count) == 3'd7) && enable) |-> (count == 3'd0)
    );

    // Any change in count (while out of reset) requires enable was HIGH in the prior cycle.
    change_requires_prev_enable: assert property (
        @(posedge clk) disable iff (!reset) ($past(reset) && (count != $past(count))) |-> $past(enable)
    );

    // With enable HIGH (while out of reset), count must change from the prior cycle.
    enable_implies_change: assert property (
        @(posedge clk) disable iff (!reset) ($past(reset) && enable) |-> (count != $past(count))
    );

    // If enable is HIGH for two consecutive cycles, count advances by 2 modulo 8.
    two_cycle_enable_increments_by_two: assert property (
        @(posedge clk) disable iff (!reset) ($past(reset,2) && $past(enable) && enable) |-> (count == (($past(count,2) + 3'd2)[2:0]))
    );
endmodule