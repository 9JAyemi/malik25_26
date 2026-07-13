module up_counter_sva (
    input logic clk,
    input logic rst_n,
    input logic [15:0] count
);
    // Clock: clk (posedge). Reset: rst_n (active-low, synchronous).
    // Sequential 16-bit up-counter with wraparound.

    // When reset is asserted low, count must be zero on the next cycle.
    reset_clears_next: assert property (
        @(posedge clk) (rst_n == 1'b0) |=> (count == 16'h0000)
    );

    // When reset is asserted low, count must be zero on the same cycle.
    reset_clears_now: assert property (
        @(posedge clk) (rst_n == 1'b0) |-> (count == 16'h0000)
    );

    // When not in reset, count increments by 1 on the next cycle.
    increment_when_running: assert property (
        @(posedge clk) disable iff (!rst_n) 1'b1 |=> (count == ($past(count) + 16'd1))
    );

    // When not in reset, count never holds its value on the next cycle.
    no_hold_when_running: assert property (
        @(posedge clk) disable iff (!rst_n) 1'b1 |=> (count != $past(count))
    );

    // When not in reset, count wraps from 16'hFFFF to 16'h0000.
    wrap_from_max: assert property (
        @(posedge clk) disable iff (!rst_n) ($past(count) == 16'hFFFF) |-> (count == 16'h0000)
    );

    // When not in reset, count is always odd on the next cycle.
    next_is_odd_when_running: assert property (
        @(posedge clk) disable iff (!rst_n) 1'b1 |=> (count[0] == 1'b1)
    );

    // When not in reset, count is always even on the same cycle.
    current_is_even_when_running: assert property (
        @(posedge clk) disable iff (!rst_n) 1'b1 |-> (count[0] == 1'b0)
    );

    // When not in reset, count is always non-zero on the next cycle.
    next_is_nonzero_when_running: assert property (
        @(posedge clk) disable iff (!rst_n) 1'b1 |=> (count != 16'h0000)
    );

    // When not in reset, count is always non-zero on the same cycle.
    current_is_nonzero_when_running: assert property (
        @(posedge clk) disable iff (!rst_n) 1'b1 |-> (count != 16'h0000)
    );

    // When not in reset, count is always within 16-bit range on the next cycle.
    next_in_range_when_running: assert property (
        @(posedge clk) disable iff (!rst_n) 1'b1 |=> (count inside {[16'h0000:16'hFFFF]})
    );

    // When not in reset, count is always within 16-bit range on the same cycle.
    current_in_range_when_running: assert property (
        @(posedge clk) disable iff (!rst_n) 1'b1 |-> (count inside {[16'h0000:16'hFFFF]})
    );
endmodule