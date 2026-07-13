module counter_sva (
    input logic clk,
    input logic reset,          // active-high synchronous reset
    input logic [7:0] max_count,
    input logic [7:0] count
);

    // Reset drives count to 0 on the next clock.
    reset_clears_next: assert property (
        @(posedge clk) reset |=> (count == 8'd0)
    );

    // When count equals max_count, next count wraps to 0.
    wrap_to_zero_at_max: assert property (
        @(posedge clk) disable iff (reset) (count == max_count) |=> (count == 8'd0)
    );

    // When count is not max_count, next count increments by 1 (mod 256).
    increment_when_not_max: assert property (
        @(posedge clk) disable iff (reset) (count != max_count) |=> (count == $past(count) + 8'd1)
    );

    // Next-state equals 0 at max_count else equals previous+1.
    next_state_equation: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (count == (($past(count) == $past(max_count)) ? 8'd0 : ($past(count) + 8'd1)))
    );

    // Count only holds across cycles when previous count==0 and previous max_count==0.
    hold_only_when_max_zero: assert property (
        @(posedge clk) disable iff (reset) (count == $past(count)) |-> (($past(count) == 8'd0) && ($past(max_count) == 8'd0))
    );

    // If count is 0 (and previous cycle not in reset), cause was max hit or 8'hFF overflow.
    zero_has_expected_causes: assert property (
        @(posedge clk) disable iff (reset) ($past(!reset) && (count == 8'd0)) |-> (($past(count) == $past(max_count)) || ($past(count) == 8'hFF))
    );

    // From 0 when max_count != 0, next count becomes 1.
    zero_then_one_when_max_nonzero: assert property (
        @(posedge clk) disable iff (reset) (count == 8'd0 && max_count != 8'd0) |=> (count == 8'd1)
    );

    // Overflow case: from 8'hFF when not at max_count, next count becomes 0.
    overflow_ff_to_zero: assert property (
        @(posedge clk) disable iff (reset) ($past(count) == 8'hFF && ($past(count) != $past(max_count))) |-> (count == 8'd0)
    );

    // Normal increment cannot produce 0 unless previous was 8'hFF.
    normal_increment_never_zero: assert property (
        @(posedge clk) disable iff (reset) ($past(count) != $past(max_count) && $past(count) != 8'hFF) |-> (count != 8'd0)
    );

    // Special case of hold: if previous count==0 and previous max_count==0, current count is 0.
    hold_when_max_zero_prev: assert property (
        @(posedge clk) disable iff (reset) ($past(count) == 8'd0 && $past(max_count) == 8'd0) |-> (count == 8'd0)
    );

endmodule