module counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] count,
    input logic overflow
);
    // Reset drives count and overflow low on the next cycle.
    reset_clears_next: assert property (
        @(posedge clk) reset |=> (count == 4'b0000) && (overflow == 1'b0)
    );

    // When enabled and not at max, count increments by 1 and overflow stays 0.
    inc_when_enabled_not_max: assert property (
        @(posedge clk) disable iff (reset)
            (enable && (count != 4'hF)) |=> (count == $past(count) + 4'd1) && (overflow == 1'b0)
    );

    // When enabled and at max, count wraps to 0 and overflow sets.
    wrap_when_enabled_at_max: assert property (
        @(posedge clk) disable iff (reset)
            (enable && (count == 4'hF)) |=> (count == 4'h0) && (overflow == 1'b1)
    );

    // When not enabled, count holds its value and overflow stays 0.
    hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
            (!enable) |=> (count == $past(count)) && (overflow == 1'b0)
    );

    // Overflow can only be 1 when previous cycle was enabled and count was 4'hF.
    overflow_implies_prev_enable_and_max: assert property (
        @(posedge clk) disable iff (reset)
            overflow |-> ($past(enable) && ($past(count) == 4'hF))
    );

    // Overflow is a single-cycle pulse.
    overflow_single_cycle_pulse: assert property (
        @(posedge clk) disable iff (reset)
            overflow |=> !overflow
    );

    // Overflow implies count is 0 on the next cycle.
    overflow_implies_next_count_zero: assert property (
        @(posedge clk) disable iff (reset)
            overflow |=> (count == 4'h0)
    );

    // Overflow implies count is 0 on the current cycle.
    overflow_implies_count_zero_now: assert property (
        @(posedge clk) disable iff (reset)
            overflow |-> (count == 4'h0)
    );

    // If count is 0 and previous cycle was not reset, previous count was 4'hF.
    zero_count_implies_prev_max_no_reset: assert property (
        @(posedge clk) disable iff (reset)
            (count == 4'h0 && $past(!reset)) |-> ($past(count) == 4'hF)
    );

    // If count is 0 and previous cycle was reset, count stays 0 on the next cycle.
    zero_count_stays_zero_after_reset: assert property (
        @(posedge clk) disable iff (reset)
            (count == 4'h0 && $past(reset)) |=> (count == 4'h0)
    );
endmodule