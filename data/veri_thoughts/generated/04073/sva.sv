module RCB_FRL_count_to_16x_sva (
    input logic       clk,
    input logic       rst,
    input logic       count,
    input logic [3:0] counter_value
);

    // A sampled reset must leave the counter at zero on the next sampled clock.
    check_reset_forces_zero_next_cycle: assert property (
        @(posedge clk) rst |=> (counter_value == 4'h0)
    );

    // Without count, the counter either holds or has been asynchronously cleared to zero.
    check_hold_or_async_reset_zero: assert property (
        @(posedge clk) disable iff (rst)
        (!count) |=> ((counter_value == $past(counter_value)) || (counter_value == 4'h0))
    );

    // With count asserted below 15, the counter either increments or has been asynchronously cleared to zero.
    check_increment_or_async_reset_zero: assert property (
        @(posedge clk) disable iff (rst)
        (count && (counter_value != 4'hf)) |=> ((counter_value == ($past(counter_value) + 4'h1)) || (counter_value == 4'h0))
    );

    // Counting from 15 wraps the 4-bit counter back to zero.
    check_wrap_from_f_to_zero: assert property (
        @(posedge clk) disable iff (rst)
        (count && (counter_value == 4'hf)) |=> (counter_value == 4'h0)
    );

    // Any nonzero change between sampled clocks must be a single-step increment caused by count.
    check_nonzero_change_is_increment: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        ((counter_value != 4'h0) && (counter_value != $past(counter_value))) |->
            ($past(count) && (counter_value == ($past(counter_value) + 4'h1)))
    );

    // Any retained nonzero value between sampled clocks must come from count being low.
    check_nonzero_hold_requires_no_count: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        ((counter_value != 4'h0) && (counter_value == $past(counter_value))) |->
            (!$past(count))
    );

endmodule