module counter_sva (
    input logic clk,
    input logic reset,           // active-high synchronous reset
    input logic [31:0] max_value,
    input logic [31:0] count
);
    // On any cycle with reset asserted, count must be 0 on the next cycle.
    reset_clears_count_next: assert property (
        @(posedge clk) reset |=> (count == 32'd0)
    );

    // If reset was 1 in the previous cycle, count must be 0 now.
    prev_reset_forces_zero_now: assert property (
        @(posedge clk) $past(reset) |-> (count == 32'd0)
    );

    // When not in reset, reaching max_value causes wrap to 0 on the next cycle.
    wrap_on_reaching_max: assert property (
        @(posedge clk) disable iff (reset) (count == max_value) |=> (count == 32'd0)
    );

    // When not in reset and below max_value, next cycle increments unless reset arrives.
    increment_when_below_max: assert property (
        @(posedge clk) disable iff (reset) (count != max_value) |=> (reset || (count == $past(count) + 32'd1))
    );

    // When not in reset and max_value==0 at 0, the counter holds at 0.
    hold_zero_when_max_zero: assert property (
        @(posedge clk) disable iff (reset) (count == 32'd0 && max_value == 32'd0) |=> (count == 32'd0)
    );

    // With reset low in consecutive cycles, next-state follows exact update rule (wrap or increment).
    precise_update_no_reset: assert property (
        @(posedge clk) (!$past(reset) && !reset) |-> (
            (count == 32'd0 && $past(count) == $past(max_value)) ||
            (count == $past(count) + 32'd1 && $past(count) != $past(max_value))
        )
    );

    // One-below-max steps to max on the next cycle when not reset (or is 0 if reset).
    step_to_max_from_one_below: assert property (
        @(posedge clk) disable iff (reset) ((count + 32'd1) == max_value && (count != max_value)) |=> (reset || (count == max_value))
    );
endmodule