module up_counter_2bit_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [1:0] count
);

    // Reset holds the counter at zero.
    check_reset_holds_zero: assert property (
        @(posedge clk) reset |-> (count == 2'b00)
    );

    // A sampled reset leaves the counter at zero on the next clock.
    check_zero_after_sampled_reset: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(reset)) |-> (count == 2'b00)
    );

    // An enabled cycle increments the count, unless reset forced it to zero.
    check_enable_increments_or_resets: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(!reset && enable)) |-> ((count == ($past(count) + 2'b01)) || (count == 2'b00))
    );

    // A disabled cycle holds the count, unless reset forced it to zero.
    check_disable_holds_or_resets: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(!reset && !enable)) |-> ((count == $past(count)) || (count == 2'b00))
    );

    // The 2-bit counter wraps from 3 back to 0 when enabled.
    check_wrap_from_max_to_zero: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(!reset && enable && (count == 2'b11))) |-> (count == 2'b00)
    );

    // Any observed count change is either an increment or a reset to zero.
    check_count_change_is_increment_or_reset: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && (count != $past(count))) |-> ((count == ($past(count) + 2'b01)) || (count == 2'b00))
    );

endmodule