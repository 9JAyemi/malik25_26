module counter_4bit_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] count
);

    // Reset forces count to zero by the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // The first cycle after reset deassertion still presents zero.
    check_zero_after_reset: assert property (
        @(posedge clk) disable iff (reset)
        ($past(reset) === 1'b1) |-> (count == 4'b0000)
    );

    // When active and below 15, count increments by one each cycle.
    check_increment_before_max: assert property (
        @(posedge clk) disable iff (reset)
        ($past(reset) === 1'b0) && ($past(count) != 4'hF) |-> (count == ($past(count) + 4'd1))
    );

    // When active at 15, count wraps to zero on the next cycle.
    check_wrap_after_max: assert property (
        @(posedge clk) disable iff (reset)
        ($past(reset) === 1'b0) && ($past(count) == 4'hF) |-> (count == 4'h0)
    );

endmodule