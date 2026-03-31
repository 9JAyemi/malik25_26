module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);
    // Clock: clk (posedge). Reset: rst (synchronous, active-high). Logic: sequential 4-bit up-counter.

    // Reset drives count to zero on the next cycle.
    reset_clears_next: assert property (
        @(posedge clk) rst |=> (count == 4'b0000)
    );

    // When not in reset, count increments by 1 each cycle (mod 16).
    count_increments_when_not_reset: assert property (
        @(posedge clk) disable iff (rst) count == $past(count) + 4'd1
    );

    // On reset deassertion, count becomes 1 on the next cycle.
    deassert_reset_sets_one: assert property (
        @(posedge clk) $fell(rst) |=> (count == 4'd1)
    );

    // If count is 0 and not in reset, it must have wrapped from 15.
    zero_only_from_wrap: assert property (
        @(posedge clk) disable iff (rst) (count == 4'd0) |-> ($past(count) == 4'd15)
    );

    // If count is 15 and not in reset, it must have incremented from 14.
    fifteen_only_from_wrap: assert property (
        @(posedge clk) disable iff (rst) (count == 4'd15) |-> ($past(count) == 4'd14)
    );

    // In normal operation, count changes every cycle.
    count_changes_each_cycle: assert property (
        @(posedge clk) disable iff (rst) count != $past(count)
    );

    // In normal operation, count never holds its value.
    count_never_stable: assert property (
        @(posedge clk) disable iff (rst) count != $past(count)
    );

    // In normal operation, count is always within 0..15.
    count_range_when_not_reset: assert property (
        @(posedge clk) disable iff (rst) count inside {[4'd0:4'd15]}
    );

    // In normal operation, count is strictly increasing (mod 16).
    count_strictly_increasing: assert property (
        @(posedge clk) disable iff (rst) count > $past(count)
    );

    // On reset assertion, count is 0 on the next cycle.
    assert_reset_sets_zero_next: assert property (
        @(posedge clk) $rose(rst) |=> (count == 4'd0)
    );

endmodule