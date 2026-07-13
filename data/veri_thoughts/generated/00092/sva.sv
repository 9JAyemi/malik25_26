module up_down_counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic up_down,
    input logic [3:0] count
);

    // Reset drives the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // When not enabled, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        (!enable) |=> (count == $past(count))
    );

    // In up mode, the counter increments when below 15.
    check_increment_in_up_mode: assert property (
        @(posedge clk) disable iff (reset)
        (enable && up_down && (count != 4'b1111)) |=> (count == ($past(count) + 4'b0001))
    );

    // In up mode, the counter wraps from 15 to 0.
    check_wrap_in_up_mode: assert property (
        @(posedge clk) disable iff (reset)
        (enable && up_down && (count == 4'b1111)) |=> (count == 4'b0000)
    );

    // In down mode, the counter decrements when above 0.
    check_decrement_in_down_mode: assert property (
        @(posedge clk) disable iff (reset)
        (enable && !up_down && (count != 4'b0000)) |=> (count == ($past(count) - 4'b0001))
    );

    // In down mode, the counter wraps from 0 to 15.
    check_wrap_in_down_mode: assert property (
        @(posedge clk) disable iff (reset)
        (enable && !up_down && (count == 4'b0000)) |=> (count == 4'b1111)
    );

endmodule