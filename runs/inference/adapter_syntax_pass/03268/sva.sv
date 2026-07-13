module binary_counter_sva (
    input logic clk,
    input logic [3:0] reset,
    input logic [3:0] enable,
    input logic [3:0] count
);

    // Reset forces count to zero on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'h0)
    );

    // Reset has priority over enable when both are asserted.
    check_reset_priority_over_enable: assert property (
        @(posedge clk) (reset && enable) |=> (count == 4'h0)
    );

    // Enable increments count by one when reset is low.
    check_enable_increments_count: assert property (
        @(posedge clk) disable iff (reset) enable |=> (count == ($past(count) + 4'd1))
    );

    // Count holds its value when neither reset nor enable is asserted.
    check_count_holds_when_idle: assert property (
        @(posedge clk) disable iff (reset) (!enable) |=> (count == $past(count))
    );

endmodule