module up_down_counter_sva (
    input logic       clk,
    input logic       areset,
    input logic       load,
    input logic       up_down,
    input logic       count_enable,
    input logic [3:0] count_out
);

    // Reset drives the counter to zero by the next clock.
    check_reset_clears_counter: assert property (
        @(posedge clk) !areset |=> (count_out == 4'b0000)
    );

    // Load clears the counter to zero on the next clock.
    check_load_clears_counter: assert property (
        @(posedge clk) disable iff (!areset)
        load |=> (count_out == 4'b0000)
    );

    // Counting up increments the counter by one.
    check_count_up_increments: assert property (
        @(posedge clk) disable iff (!areset)
        (!load && count_enable && up_down) |=> (count_out == ($past(count_out) + 4'b0001))
    );

    // Counting down decrements the counter by one.
    check_count_down_decrements: assert property (
        @(posedge clk) disable iff (!areset)
        (!load && count_enable && !up_down) |=> (count_out == ($past(count_out) - 4'b0001))
    );

    // Without load or count enable, the counter holds its value.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (!areset)
        (!load && !count_enable) |=> (count_out == $past(count_out))
    );

    // Counting up wraps from 15 back to 0.
    check_count_up_wraps: assert property (
        @(posedge clk) disable iff (!areset)
        (!load && count_enable && up_down && (count_out == 4'hF)) |=> (count_out == 4'h0)
    );

    // Counting down wraps from 0 back to 15.
    check_count_down_wraps: assert property (
        @(posedge clk) disable iff (!areset)
        (!load && count_enable && !up_down && (count_out == 4'h0)) |=> (count_out == 4'hF)
    );

endmodule