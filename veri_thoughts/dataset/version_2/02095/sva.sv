module counter_sva (
    input logic clk,
    input logic rst,
    input logic [31:0] max_val,
    input logic [31:0] count
);
    // Reset drives count to 0 on the next rising edge.
    reset_clears_count_next: assert property (
        @(posedge clk) rst |=> (count == 32'd0)
    );

    // When count equals max_val (no reset), next value is 0.
    wrap_to_zero_on_max: assert property (
        @(posedge clk) disable iff (rst) (count == max_val) |=> (count == 32'd0)
    );

    // When count is not max_val (no reset), next value increments by 1.
    increment_when_not_max: assert property (
        @(posedge clk) disable iff (rst) (count != max_val) |=> (count == $past(count) + 32'd1)
    );

    // Next value function is exactly: (count==max_val) ? 0 : count+1 (no reset).
    deterministic_update: assert property (
        @(posedge clk) disable iff (rst) 1 |=> (count == (($past(count) == $past(max_val)) ? 32'd0 : $past(count) + 32'd1))
    );

    // If not due to reset, a 0 value must come from prior equality to max or overflow.
    zero_implies_prev_eq_max_or_overflow: assert property (
        @(posedge clk) disable iff (rst) 1 |=> ((count == 32'd0 && !$past(rst)) -> ($past(count) == $past(max_val) || $past(count) == 32'hFFFF_FFFF))
    );

    // If previous count was neither max_val nor 32'hFFFF_FFFF (no reset), next count is not 0.
    no_zero_without_eq_or_overflow: assert property (
        @(posedge clk) disable iff (rst) 1 |=> (($past(count) != $past(max_val) && $past(count) != 32'hFFFF_FFFF) -> (count != 32'd0))
    );
endmodule