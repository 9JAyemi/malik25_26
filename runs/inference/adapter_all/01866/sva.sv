module up_counter_sva (
    input logic clk,
    input logic rst_n,
    input logic [15:0] count
);
    // Clock: clk (posedge). Reset: rst_n active-low, asynchronous. Sequential 16-bit up-counter.

    // When reset is asserted, count must be 0 on the next cycle.
    reset_clears_next: assert property (
        @(posedge clk) !rst_n |=> (count == 16'h0000)
    );

    // While reset is held low across cycles, count remains 0.
    hold_zero_while_reset: assert property (
        @(posedge clk) (!rst_n && $past(!rst_n)) |-> (count == 16'h0000)
    );

    // On the cycle reset deasserts, count becomes 1.
    count_one_on_reset_release: assert property (
        @(posedge clk) $rose(rst_n) |-> (count == 16'h0001)
    );

    // When not in reset for two consecutive cycles, count increments by 1.
    count_increments_when_running: assert property (
        @(posedge clk) disable iff (!rst_n) $past(rst_n) |-> (count == $past(count) + 16'd1)
    );

    // When not in reset for two consecutive cycles, count changes every cycle.
    count_changes_each_cycle_running: assert property (
        @(posedge clk) disable iff (!rst_n) $past(rst_n) |-> (count != $past(count))
    );

    // When not in reset for two consecutive cycles, count wraps from 0xFFFF to 0x0000.
    count_wraps_from_max: assert property (
        @(posedge clk) disable iff (!rst_n) ($past(rst_n) && ($past(count) == 16'hFFFF)) |-> (count == 16'h0000)
    );

    // On reset deassertion, the next value is 1 (not 0) because the increment occurs before the next clock edge.
    next_value_one_after_reset_release: assert property (
        @(posedge clk) $rose(rst_n) |=> (count == 16'h0001)
    );

    // If reset is held low for 16 cycles, count is 0 on the 16th cycle.
    hold_low_for_16_cycles: assert property (
        @(posedge clk) (!rst_n)[*16] |-> (count == 16'h0000)
    );

    // If reset is held low for 17 cycles, count is still 0 on the 17th cycle.
    hold_low_for_17_cycles: assert property (
        @(posedge clk) (!rst_n)[*17] |-> (count == 16'h0000)
    );

    // If reset is held low for 18 cycles, count is still 0 on the 18th cycle.
    hold_low_for_18_cycles: assert property (
        @(posedge clk) (!rst_n)[*18] |-> (count == 16'h0000)
    );

endmodule