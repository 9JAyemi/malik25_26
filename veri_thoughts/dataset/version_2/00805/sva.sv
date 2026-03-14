module counter_3bit_async_reset_sva (
    input logic clk,
    input logic rst,
    input logic [2:0] count
);
    ///// Reset behavior /////
    // When reset is asserted LOW at a clock edge, count is forced to 0.
    check_reset_forces_zero: assert property (
        @(posedge clk) !rst |-> (count == 3'd0)
    );

    // While reset remains LOW across consecutive cycles, count holds at 0 (stable).
    check_reset_held_low_stable: assert property (
        @(posedge clk) ($past(1'b1) && !rst && $past(!rst)) |-> ($stable(count) && (count == 3'd0))
    );

    // On the first clock after reset deasserts (LOW->HIGH across clocks), count becomes 1.
    check_release_to_one: assert property (
        @(posedge clk) disable iff (!rst) ($past(1'b1) && $past(!rst) && rst) |-> (count == 3'd1)
    );

    // If the previous cycle had reset LOW, then the previous count was 0.
    check_prev_cycle_reset_count_zero: assert property (
        @(posedge clk) ($past(1'b1) && $past(!rst)) |-> ($past(count) == 3'd0)
    );

    // From a cycle with reset LOW, the next cycle's count is 0 if reset stays LOW, else 1 if reset goes HIGH.
    check_next_cycle_after_reset: assert property (
        @(posedge clk) !rst |-> ##1 ((rst && (count == 3'd1)) || (!rst && (count == 3'd0)))
    );

    // When not in reset and count is 0 at a clock edge, it must be due to wrap from 7.
    check_wrap_to_zero_requires_prev_seven: assert property (
        @(posedge clk) disable iff (!rst) ($past(1'b1) && rst && (count == 3'd0)) |-> ($past(count) == 3'd7)
    );
endmodule