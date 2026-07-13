module counter_sva (
    input logic clk,
    input logic reset,
    input logic [31:0] max_count,
    input logic [31:0] count
);

    // Synchronous reset drives count to 0 on the next cycle.
    reset_sets_zero_next: assert property (
        @(posedge clk) reset |=> (count == 32'd0)
    );

    // If reset is held across consecutive cycles, count is 0 on the later cycle.
    reset_held_keeps_zero: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (count == 32'd0)
    );

    // On reset deassertion (prior cycle asserted, now deasserted), count is 0.
    reset_release_zero: assert property (
        @(posedge clk) ($past(reset) && !reset) |-> (count == 32'd0)
    );

    // When not in reset: if prior count == prior max_count, next count is 0 (wrap).
    wrap_on_match_prev: assert property (
        @(posedge clk) disable iff (reset)
            ($past(count) == $past(max_count)) |-> (count == 32'd0)
    );

    // When not in reset: if prior count != prior max_count, next count increments by 1.
    increment_on_neq_prev: assert property (
        @(posedge clk) disable iff (reset)
            ($past(count) != $past(max_count)) |-> (count == ($past(count) + 32'd1))
    );

    // When not in reset: next count matches the RTL branching (wrap or increment).
    next_value_follows_rtl: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset)) |-> (count == (($past(count) == $past(max_count)) ? 32'd0 : ($past(count) + 32'd1)))
    );

endmodule