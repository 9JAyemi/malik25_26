module binary_counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] count
);
    // Synchronous reset drives count to 0 in the same cycle it is asserted.
    reset_clears_now: assert property (
        @(posedge clk) reset |-> (count == 4'd0)
    );

    // If reset was high in the previous cycle, count is 0 now.
    reset_prev_sets_zero: assert property (
        @(posedge clk) disable iff (reset) $past(reset) |-> (count == 4'd0)
    );

    // With no reset, enable in the previous cycle increments count by 1 (mod 16).
    inc_on_enable: assert property (
        @(posedge clk) disable iff (reset) $past(!reset && enable) |-> (count == $past(count) + 4'd1)
    );

    // With no reset, no enable in the previous cycle holds count steady.
    hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset) $past(!reset && !enable) |-> (count == $past(count))
    );

    // Any change in count must come from previous enable with no reset and be +1.
    change_implies_enable_and_plus1: assert property (
        @(posedge clk) disable iff (reset) (count != $past(count)) |-> ($past(!reset && enable) && (count == $past(count) + 4'd1))
    );

    // From 4'hF with enable and no reset, wrap to 0 on the next cycle.
    wrap_on_max: assert property (
        @(posedge clk) disable iff (reset) $past(!reset && enable && (count == 4'hF)) |-> (count == 4'h0)
    );

    // Immediately after reset deasserts, if enable is 0, count remains 0.
    post_reset_hold_zero_if_no_enable: assert property (
        @(posedge clk) disable iff (reset) ($past(reset) && !reset && !enable) |-> (count == 4'd0)
    );

    // Two consecutive enabled cycles without reset cause a +2 total increment.
    two_cycle_increment: assert property (
        @(posedge clk) disable iff (reset) ($past(!reset && enable, 1) && $past(!reset && enable, 2)) |-> (count == $past(count, 2) + 4'd2)
    );

    // Two consecutive disabled cycles without reset hold count over both cycles.
    two_cycle_hold: assert property (
        @(posedge clk) disable iff (reset) ($past(!reset && !enable, 1) && $past(!reset && !enable, 2)) |-> (count == $past(count, 2))
    );

    // Reset has priority over enable when both were asserted in the previous cycle.
    reset_overrides_enable: assert property (
        @(posedge clk) disable iff (reset) $past(reset && enable) |-> (count == 4'd0)
    );
endmodule