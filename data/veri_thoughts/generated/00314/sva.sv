module up_counter_sva (
    input logic [3:0] count,
    input logic       clk,
    input logic       reset
);

    // Active-low reset forces count to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) !reset |-> (count == 4'b0000)
    );

    // The first sampled cycle after reset release still sees count at zero.
    check_release_from_reset_starts_at_zero: assert property (
        @(posedge clk) disable iff (!reset)
        (!$initstate && !$past(reset)) |-> (count == 4'b0000)
    );

    // From a non-max value, count advances by one unless reset occurred between clocks.
    check_increment_or_async_clear_from_nonmax: assert property (
        @(posedge clk) disable iff (!reset)
        (!$initstate && $past(reset) && ($past(count) != 4'hF)) |->
        ((count == ($past(count) + 4'd1)) || (count == 4'b0000))
    );

    // From 4'hF, the sampled next value must wrap to zero.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (!reset)
        (!$initstate && $past(reset) && ($past(count) == 4'hF)) |-> (count == 4'b0000)
    );

endmodule