module counter_4bit_sva (
    input logic       clk,
    input logic       rst_n,
    input logic       enable,
    input logic       count_up,
    input logic [3:0] q
);

    // Sequential 4-bit counter on clk with active-low reset rst_n.

    // Active-low reset forces q to zero.
    check_reset_clears_q: assert property (
        @(posedge clk)
        (!rst_n) |-> (q == 4'b0000)
    );

    // q holds its value when enable is low.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (!rst_n)
        (!enable) |=> (q == $past(q))
    );

    // q increments by one when enabled and counting up.
    check_increment_when_enabled_up: assert property (
        @(posedge clk) disable iff (!rst_n)
        (enable && count_up) |=> (q == ($past(q) + 4'd1))
    );

    // q decrements by one when enabled and counting down.
    check_decrement_when_enabled_down: assert property (
        @(posedge clk) disable iff (!rst_n)
        (enable && !count_up) |=> (q == ($past(q) - 4'd1))
    );

    // Counting up wraps from 15 to 0.
    check_wrap_up_from_max: assert property (
        @(posedge clk) disable iff (!rst_n)
        (enable && count_up && (q == 4'hF)) |=> (q == 4'h0)
    );

    // Counting down wraps from 0 to 15.
    check_wrap_down_from_zero: assert property (
        @(posedge clk) disable iff (!rst_n)
        (enable && !count_up && (q == 4'h0)) |=> (q == 4'hF)
    );

endmodule