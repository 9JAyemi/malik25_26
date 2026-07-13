module counter_sva (
    input logic       clk,
    input logic [3:0] reset,
    input logic [3:0] count
);

    // A non-zero reset clears the counter on the following clock.
    check_reset_clears_count: assert property (
        @(posedge clk) (reset != 4'h0) |=> (count == 4'h0)
    );

    // After a reset cycle, count is zero once reset is low again.
    check_count_zero_after_reset: assert property (
        @(posedge clk) disable iff (reset != 4'h0)
        !$initstate && $past(reset != 4'h0) |-> (count == 4'h0)
    );

    // When not resetting, a non-maximum count increments by one.
    check_count_advances_nonmax: assert property (
        @(posedge clk) disable iff (reset != 4'h0)
        !$initstate && !$past(reset != 4'h0) && ($past(count) != 4'hF) |-> (count == ($past(count) + 4'h1))
    );

    // When not resetting, 4'hF wraps back to zero.
    check_count_wraps_from_max: assert property (
        @(posedge clk) disable iff (reset != 4'h0)
        !$initstate && !$past(reset != 4'h0) && ($past(count) == 4'hF) |-> (count == 4'h0)
    );

endmodule