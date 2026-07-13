module counter_4bit_async_reset_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);
    // Clock: clk (posedge). Reset: rst (active-low, asynchronous). Logic: sequential counter with async reset.

    // While reset is asserted, count must be 0.
    check_reset_forces_zero: assert property (
        @(posedge clk) !rst |-> (count == 4'b0000)
    );

    // On reset deassertion, count becomes 1 in the same cycle.
    check_reset_release_sets_one: assert property (
        @(posedge clk) $rose(rst) |-> (count == 4'b0001)
    );

    // When not in reset, count increments by 1 each cycle (mod-16).
    check_count_increments: assert property (
        @(posedge clk) disable iff (!rst) 1'b1 |=> (count == $past(count) + 4'd1)
    );

    // When not in reset, count never exceeds 15.
    check_count_bounded: assert property (
        @(posedge clk) disable iff (!rst) count <= 4'hF
    );

    // When not in reset, count changes every cycle.
    check_count_changes_each_cycle: assert property (
        @(posedge clk) disable iff (!rst) 1'b1 |=> (count != $past(count))
    );

    // When not in reset, 0xF wraps to 0 on the next cycle.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (!rst) (count == 4'hF) |=> (count == 4'h0)
    );

    // On reset assertion, count is 0 in the same cycle.
    check_reset_assertion_clears: assert property (
        @(posedge clk) $fell(rst) |-> (count == 4'b0000)
    );

    // On reset deassertion, count is 1 in the same cycle.
    check_reset_release_sets_one_now: assert property (
        @(posedge clk) $rose(rst) |-> (count == 4'b0001)
    );

    // On reset deassertion, count is 1 in the next cycle.
    check_reset_release_increments_next: assert property (
        @(posedge clk) $rose(rst) |=> (count == 4'b0001)
    );

    // When not in reset, count changes every cycle (no hold).
    check_no_hold_when_not_reset: assert property (
        @(posedge clk) disable iff (!rst) 1'b1 |=> (count != $past(count))
    );
endmodule