module up_down_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic       up_down,
    input logic [3:0] count_out
);

    // A sampled reset forces the counter to zero by the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count_out == 4'h0)
    );

    // When up_down is high, the counter increments by one.
    check_count_increments: assert property (
        @(posedge clk) disable iff (reset)
        up_down |=> (count_out == ($past(count_out) + 4'h1))
    );

    // When up_down is low, the counter decrements by one.
    check_count_decrements: assert property (
        @(posedge clk) disable iff (reset)
        !up_down |=> (count_out == ($past(count_out) - 4'h1))
    );

    // The counter wraps from 15 to 0 when counting up.
    check_count_wraps_up: assert property (
        @(posedge clk) disable iff (reset)
        (up_down && (count_out == 4'hF)) |=> (count_out == 4'h0)
    );

    // The counter wraps from 0 to 15 when counting down.
    check_count_wraps_down: assert property (
        @(posedge clk) disable iff (reset)
        (!up_down && (count_out == 4'h0)) |=> (count_out == 4'hF)
    );

endmodule