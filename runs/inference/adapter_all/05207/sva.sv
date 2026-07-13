module sync_reset_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);
    // During active-low reset, count must be 0.
    reset_forces_zero: assert property (
        @(posedge clk) !rst |-> (count == 4'd0)
    );

    // On reset deassertion, count becomes 1 in the same cycle.
    count_one_on_reset_release: assert property (
        @(posedge clk) $rose(rst) |-> (count == 4'd1)
    );

    // When not in reset, count increments by 1 each cycle (mod 16).
    count_increments_when_not_reset: assert property (
        @(posedge clk) disable iff (!rst) count == $past(count) + 4'd1
    );

    // When not in reset, count never holds its value (must change).
    count_changes_each_cycle: assert property (
        @(posedge clk) disable iff (!rst) count != $past(count)
    );

    // When not in reset, count wraps from 15 to 0.
    count_wraps_from_max: assert property (
        @(posedge clk) disable iff (!rst) ($past(count) == 4'hF) |-> (count == 4'h0)
    );

    // If count is 0 while not in reset, the previous value was 15.
    zero_implies_prev_max: assert property (
        @(posedge clk) disable iff (!rst) (count == 4'h0) |-> ($past(count) == 4'hF)
    );

    // If count is 1 while not in reset, the previous value was 0.
    one_implies_prev_zero: assert property (
        @(posedge clk) disable iff (!rst) (count == 4'h1) |-> ($past(count) == 4'h0)
    );

    // If count is 2 while not in reset, the previous value was 1.
    two_implies_prev_one: assert property (
        @(posedge clk) disable iff (!rst) (count == 4'h2) |-> ($past(count) == 4'h1)
    );

    // If count is 15 while not in reset, the previous value was 14.
    max_implies_prev_min: assert property (
        @(posedge clk) disable iff (!rst) (count == 4'hF) |-> ($past(count) == 4'he)
    );

    // If count is 14 while not in reset, the next value is 15.
    min_implies_next_max: assert property (
        @(posedge clk) disable iff (!rst) (count == 4'he) |-> ##1 (count == 4'hF)
    );
endmodule