module counter_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] count
);

    // Synchronous reset drives count to zero on the next clock.
    check_reset_clears_next: assert property (
        @(posedge clk) reset |=> (count == 8'h00)
    );

    // While reset is held across cycles, count remains zero.
    check_reset_held_forces_zero: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (count == 8'h00)
    );

    // When not in reset and previous count was not 0xFF, count increments by 1.
    check_increment_no_wrap: assert property (
        @(posedge clk) disable iff (reset)
            ($past(count) != 8'hFF) |-> (count == $past(count) + 8'd1)
    );

    // When not in reset and previous count was 0xFF, count wraps to 0x00.
    check_wrap_from_ff: assert property (
        @(posedge clk) disable iff (reset)
            ($past(count) == 8'hFF) |-> (count == 8'h00)
    );

    // On reset deassertion (1->0), the first not-reset cycle produces count == 1.
    check_first_cycle_after_reset_deassert: assert property (
        @(posedge clk) disable iff (reset)
            $fell(reset) |-> (count == 8'h01)
    );

    // When not in reset and no wrap, count strictly increases.
    check_monotonic_increase_no_wrap: assert property (
        @(posedge clk) disable iff (reset)
            ($past(count) != 8'hFF) |-> (count > $past(count))
    );

endmodule