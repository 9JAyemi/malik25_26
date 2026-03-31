module up_counter_sva (
    input logic clk,
    input logic rst_n,
    input logic [15:0] count
);
    // Count is cleared to 0 whenever rst_n is LOW (synchronous reset).
    reset_clears_count: assert property (
        @(posedge clk) !rst_n |-> (count == 16'h0000)
    );

    // When not in reset, count increments by 1 each cycle (modulo 2^16).
    check_increment_by_one: assert property (
        @(posedge clk) disable iff (!rst_n) (count == $past(count) + 16'd1)
    );

    // When previous value was 0xFFFF, next value wraps to 0.
    check_wrap_at_max: assert property (
        @(posedge clk) disable iff (!rst_n) ($past(count) == 16'hFFFF) |-> (count == 16'h0000)
    );

    // On reset deassertion cycle, count updates from previous value +1.
    check_increment_on_reset_release: assert property (
        @(posedge clk) disable iff (!rst_n) $rose(rst_n) |-> (count == $past(count) + 16'd1)
    );

    // While reset remains asserted across cycles, count stays 0.
    check_hold_zero_while_in_reset: assert property (
        @(posedge clk) ($past(!rst_n) && !rst_n) |-> (count == 16'h0000)
    );
endmodule