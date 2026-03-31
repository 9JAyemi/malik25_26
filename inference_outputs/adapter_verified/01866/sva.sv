module up_counter_sva (
    input logic clk,
    input logic rst_n,
    input logic [15:0] count
);

// Clock: clk (posedge). Reset: rst_n active-low, asynchronous.
    // Behavior: 16-bit up-counter; synchronous reset clears to 0; else increments by 1.

    // On any cycle with rst_n LOW, count must be 0 on the next cycle.
    check_reset_clears_next: assert property (
        @(posedge clk) !rst_n |=> (count == 16'h0000)
    );

// If rst_n is LOW in consecutive cycles, count is 0 in the current cycle.
    check_reset_holds_zero: assert property (
        @(posedge clk) (!rst_n && $past(!rst_n)) |-> (count == 16'h0000)
    );

// If rst_n is HIGH in consecutive cycles, count increments by 1 (mod 2^16).
    check_count_increments: assert property (
        @(posedge clk) disable iff (!rst_n) $past(rst_n) |-> (count == $past(count) + 16'h0001)
    );

// If rst_n is HIGH and count is 0xFFFF, next count becomes 0 (mod 2^16).
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (!rst_n) ($past(rst_n) && ($past(count) == 16'hFFFF)) |-> (count == 16'h0000)
    );

// If rst_n is HIGH and count is not 0xFFFF, next count differs by +1 (mod 2^16).
    check_nonwrap_increments: assert property (
        @(posedge clk) disable iff (!rst_n) ($past(rst_n) && ($past(count) != 16'hFFFF)) |-> (count != $past(count) + 16'h0001)
    );

endmodule
