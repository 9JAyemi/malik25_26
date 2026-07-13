module binary_counter_sva (
    input logic reset,
    input logic load,
    input logic clk,
    input logic [3:0] data_in,
    input logic [3:0] count
);
    // Clock: clk (posedge). Reset: reset (active-high, synchronous). Logic: sequential 4-bit counter.

    // On a cycle with reset HIGH, next cycle count must be 0.
    check_reset_sets_zero_next: assert property (
        @(posedge clk) reset |-> ##1 (count == 4'd0)
    );

    // If reset stays HIGH across cycles, count is 0 on the later cycle.
    check_reset_holds_zero: assert property (
        @(posedge clk) reset && $past(reset) |-> (count == 4'd0)
    );

    // When reset and load are both HIGH, reset overrides and next cycle is 0.
    check_reset_overrides_load: assert property (
        @(posedge clk) (reset && load) |-> ##1 (count == 4'd0)
    );

    // With load HIGH and not in reset, next cycle count equals current data_in.
    check_load_updates_count: assert property (
        @(posedge clk) disable iff (reset) load |-> ##1 (count == $past(data_in))
    );

    // With load LOW and not in reset, next cycle count increments by 1 (mod 16).
    check_increment_when_idle: assert property (
        @(posedge clk) disable iff (reset) (!load) |-> ##1 (count == ($past(count) + 4'd1))
    );

    // If load remains LOW for two cycles (no reset), count advances by 2 over two cycles.
    check_double_idle_increments_by_two: assert property (
        @(posedge clk) disable iff (reset) (!load && $past(!load)) |-> (count == ($past(count,2) + 4'd2))
    );

    // If previous count was 15 and load LOW (no reset), next count wraps to 0.
    check_wraparound_from_15: assert property (
        @(posedge clk) disable iff (reset) (!load && ($past(count) == 4'hF)) |-> ##1 (count == 4'h0)
    );

    // If load is HIGH for two consecutive cycles and data_in is unchanged, count is unchanged across those cycles.
    check_consecutive_load_same_data_holds_count: assert property (
        @(posedge clk) disable iff (reset) (load && $past(load) && (data_in == $past(data_in))) |-> ##1 (count == $past(count))
    );

    // On the falling edge of reset, the current count is 0 (set by the prior cycle's reset).
    check_post_reset_count_zero: assert property (
        @(posedge clk) $fell(reset) |-> (count == 4'd0)
    );

    // Next-state function matches RTL: count(t) equals f(reset,load,data_in,count) from t-1.
    check_next_state_matches_rtl: assert property (
        @(posedge clk) $past(1'b1) |-> (count == ($past(reset) ? 4'd0
                                               : ($past(load) ? $past(data_in)
                                                              : ($past(count) + 4'd1))))
    );

endmodule