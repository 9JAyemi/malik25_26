module simple_counter_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] count
);
    // Clock: clk (posedge)
    // Reset: reset (active-high, synchronous)
    // Logic: sequential counter with wrap at 8'hFF

    // Reset drives count to 0 on the next cycle.
    reset_clears_count_next: assert property (
        @(posedge clk) reset |=> (count == 8'h00)
    );

    // If reset is held high across cycles, count is 0 in the held cycle.
    reset_held_keeps_zero: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (count == 8'h00)
    );

    // When not reset and not at max, next count increments by 1.
    count_increments_when_not_max: assert property (
        @(posedge clk) disable iff (reset) (count != 8'hFF) |=> (count == $past(count) + 8'h01)
    );

    // When not reset and at max, next count wraps to 0.
    count_wraps_after_max: assert property (
        @(posedge clk) disable iff (reset) (count == 8'hFF) |=> (count == 8'h00)
    );

    // Next-state is fully determined by current count when not in reset.
    next_state_deterministic: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (count == (($past(count) == 8'hFF) ? 8'h00 : ($past(count) + 8'h01)))
    );

    // Without reset over two adjacent cycles, count must change every cycle.
    count_changes_every_cycle_no_reset: assert property (
        @(posedge clk) disable iff (reset) (!reset && !$past(reset)) |-> (count != $past(count))
    );

    // If count is 0 without reset, previous cycle was either reset or 0xFF.
    zero_only_from_reset_or_wrap: assert property (
        @(posedge clk) disable iff (reset) (count == 8'h00) |-> ($past(reset) || ($past(count) == 8'hFF))
    );

    // If previous cycle (without reset) was 0xFF, current count is 0.
    prev_max_implies_zero_now: assert property (
        @(posedge clk) disable iff (reset) ($past(!reset) && ($past(count) == 8'hFF)) |-> (count == 8'h00)
    );

endmodule