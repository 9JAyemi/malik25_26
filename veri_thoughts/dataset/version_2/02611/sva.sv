module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);
    // While reset is asserted (active-high), count must be 0 at each clk edge.
    reset_forces_zero: assert property (
        @(posedge clk) rst |-> (count == 4'd0)
    );

    // If reset stays asserted across cycles, count remains 0 and stable.
    reset_holds_zero_stable: assert property (
        @(posedge clk) disable iff ($initstate) (rst && $past(rst)) |-> (count == 4'd0) && $stable(count)
    );

    // When reset deasserts (1->0), count becomes 1 on that clk edge.
    count_is_one_on_reset_release: assert property (
        @(posedge clk) disable iff ($initstate) $fell(rst) |-> (count == 4'd1)
    );

    // When not in reset, count must change every clk (increments or wraps).
    count_changes_every_cycle_without_reset: assert property (
        @(posedge clk) disable iff (rst || $initstate) !$stable(count)
    );

    // Without reset, if count is 0 now, it must have been 15 in the previous cycle (wrap).
    zero_now_means_prev_fifteen: assert property (
        @(posedge clk) disable iff (rst || $initstate) (count == 4'd0) |-> ($past(count) == 4'd15)
    );

    // When reset asserts (0->1), count must be 0 at that clk edge.
    reset_rise_results_zero: assert property (
        @(posedge clk) disable iff ($initstate) $rose(rst) |-> (count == 4'd0)
    );
endmodule