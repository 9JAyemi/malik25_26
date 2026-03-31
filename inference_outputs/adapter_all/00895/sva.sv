module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic [2:0] count
);
    // Clock: clk (posedge). Reset: rst (active-low, asynchronous). Sequential 3-bit counter.

    // While reset is asserted low, count must be 0.
    check_reset_forces_zero: assert property (
        @(posedge clk) (rst == 1'b0) |-> (count == 3'b000)
    );

    // On reset deassertion, count becomes 1 on the next clock.
    check_reset_release_sets_one: assert property (
        @(posedge clk) $rose(rst) |-> ##1 (count == 3'b001)
    );

    // When not in reset, count increments by 1 each cycle (mod 8).
    check_count_increments: assert property (
        @(posedge clk) disable iff (!rst) 1'b1 |-> ##1 (count == $past(count) + 3'd1)
    );

    // When not in reset, count wraps from 7 to 0.
    check_count_wraps_from_max: assert property (
        @(posedge clk) disable iff (!rst) (count == 3'b111) |-> ##1 (count == 3'b000)
    );

    // When not in reset, count changes every cycle.
    check_count_changes_each_cycle: assert property (
        @(posedge clk) disable iff (!rst) 1'b1 |-> ##1 (count != $past(count))
    );

    // When not in reset, count is always within 0..7.
    check_count_range_when_active: assert property (
        @(posedge clk) disable iff (!rst) 1'b1 |-> (count inside {[3'b000:3'b111]})
    );

    // When not in reset, count is never X/Z.
    check_count_known_when_active: assert property (
        @(posedge clk) disable iff (!rst) 1'b1 |-> !$isunknown(count)
    );

    // On reset assertion, count is 0 on the same cycle.
    check_reset_assertion_zero_now: assert property (
        @(posedge clk) $fell(rst) |-> (count == 3'b000)
    );

    // On reset deassertion, count is 0 on the same cycle.
    check_reset_release_zero_now: assert property (
        @(posedge clk) $rose(rst) |-> (count == 3'b000)
    );

    // On reset deassertion, count becomes 1 on the next cycle.
    check_reset_release_one_next: assert property (
        @(posedge clk) $rose(rst) |-> ##1 (count == 3'b001)
    );

endmodule