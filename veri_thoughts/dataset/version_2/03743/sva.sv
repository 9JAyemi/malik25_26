module binary_counter_assertions (
    input logic clk,
    input logic rst,
    input logic up_down,
    input logic [3:0] count
);

    // A sampled reset cycle leaves the counter cleared.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 4'h0)
    );

    // In up mode below 15, the counter increments by one.
    check_up_mode_increments: assert property (
        @(posedge clk) disable iff (rst)
        (up_down && (count != 4'hf)) |=> (count == ($past(count) + 4'h1))
    );

    // In up mode at 15, the counter wraps to 0.
    check_up_mode_wraps_to_zero: assert property (
        @(posedge clk) disable iff (rst)
        (up_down && (count == 4'hf)) |=> (count == 4'h0)
    );

    // In down mode above 0, the counter decrements by one.
    check_down_mode_decrements: assert property (
        @(posedge clk) disable iff (rst)
        ((!up_down) && (count != 4'h0)) |=> (count == ($past(count) - 4'h1))
    );

    // In down mode at 0, the counter wraps to 15.
    check_down_mode_wraps_to_fifteen: assert property (
        @(posedge clk) disable iff (rst)
        ((!up_down) && (count == 4'h0)) |=> (count == 4'hf)
    );

endmodule