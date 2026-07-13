module counter_4bit_async_reset_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);

// Clock: clk (posedge). Reset: rst active-low, asynchronous.
    // Behavior: 4-bit up-counter with async reset; count=0 on reset, else count+1.

    // When reset is LOW at a clock edge, count must be 0 on the next cycle.
    check_reset_forces_zero_next: assert property (
        @(posedge clk) !rst |=> (count == 4'd0)
    );

// If reset is LOW in consecutive cycles, count must be 0 in the current cycle.
    check_reset_holds_zero: assert property (
        @(posedge clk) (!rst && $past(!rst)) |-> (count == 4'd0)
    );

// If reset is LOW in the current cycle, next cycle's count is 0 (synchronous update).
    check_next_cycle_zero_after_reset: assert property (
        @(posedge clk) !rst |=> (count == 4'd0)
    );

// If reset is HIGH and count is 0, next cycle's count is 1 (synchronous update).
    check_count_increments_from_zero: assert property (
        @(posedge clk) disable iff (!rst) (count == 4'd0) |=> (count == 4'd1)
    );

// If reset is HIGH and count is 15, next cycle's count is 0 (synchronous wrap).
    check_count_wraps_from_max: assert property (
        @(posedge clk) disable iff (!rst) (count == 4'hF) |=> (count == 4'd0)
    );

// If reset is HIGH and count is not 0 or 15, next cycle's count is +1 (no wrap).
    check_count_increments_non_edge_cases: assert property (
        @(posedge clk) disable iff (!rst) (count != 4'd0 && count != 4'hF) |=> (count == $past(count) + 4'd1)
    );

endmodule
