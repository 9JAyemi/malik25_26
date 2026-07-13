module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);
    // Clock: clk; Reset: rst (active-high, asynchronous)
    // Sequential logic: 4-bit up-counter with async reset to 0

    // During reset, count is forced to 0.
    check_reset_forces_zero: assert property (
        @(posedge clk) rst |-> (count == 4'd0)
    );

    // While reset remains asserted across cycles, count stays 0 and stable.
    check_count_stable_while_reset: assert property (
        @(posedge clk) (rst && $past(rst)) |-> (count == 4'd0 && $stable(count))
    );

    // When out of reset for two consecutive cycles, count increments by 1.
    check_increment_out_of_reset: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst)) |-> (count == $past(count) + 4'd1)
    );

    // Wrap-around: when previous value was 0xF out of reset, next is 0x0.
    check_wraparound_from_f_to_0: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

    // On reset deassertion, the next clock sets count to 1.
    check_post_reset_first_increment_to_one: assert property (
        @(posedge clk) $fell(rst) |-> (count == 4'd1)
    );

    // Out of reset, any observed zero must follow a previous 0xF (no unexpected drops).
    check_zero_only_follows_f: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst) && (count == 4'd0)) |-> ($past(count) == 4'hF)
    );

    // Out of reset, count changes every cycle.
    check_count_changes_each_cycle: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst)) |-> $changed(count)
    );

endmodule