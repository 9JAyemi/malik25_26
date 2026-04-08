module counter_4bit_sva(
    input logic       clk,
    input logic       reset,
    input logic       enable,
    input logic [3:0] count
);

    // Synchronous reset clears count on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // When enabled outside reset, count increments by one.
    check_enable_increments_count: assert property (
        @(posedge clk) disable iff (reset)
        enable |=> (count == ($past(count) + 4'b0001))
    );

    // When not enabled outside reset, count holds its value.
    check_disable_holds_count: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (count == $past(count))
    );

    // Reset takes priority over enable.
    check_reset_priority_over_enable: assert property (
        @(posedge clk) (reset && enable) |=> (count == 4'b0000)
    );

    // Increment wraps from 15 back to 0.
    check_wraps_from_max: assert property (
        @(posedge clk) disable iff (reset)
        (enable && count == 4'hf) |=> (count == 4'h0)
    );

endmodule