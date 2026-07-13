module counter_sva (
    input logic clk,
    input logic reset,       // active-high synchronous reset
    input logic [3:0] count
);

    // On reset high at this clock, next cycle count must be 0.
    check_reset_clears: assert property (
        @(posedge clk) reset |=> (count == 4'h0)
    );

    // When not in reset and count != 0xF, next cycle increments by 1.
    check_increment_no_wrap: assert property (
        @(posedge clk) disable iff (reset) (count != 4'hF) |=> (count == $past(count) + 4'd1)
    );

    // When not in reset and count == 0xF, next cycle wraps to 0.
    check_increment_wrap: assert property (
        @(posedge clk) disable iff (reset) (count == 4'hF) |=> (count == 4'h0)
    );

endmodule