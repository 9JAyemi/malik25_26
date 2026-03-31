module four_bit_counter_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] count
);

// On reset, count is driven to 0 on the next clock.
    reset_clears_next: assert property (
        @(posedge clk) reset |=> (count == 4'd0)
    );

// When not in reset, count increments by 1 on the next clock.
    count_increments: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (count == ($past(count) + 4'd1))
    );

// When not in reset, count wraps from 15 back to 0.
    count_wraps_from_max: assert property (
        @(posedge clk) disable iff (reset) (count == 4'hF) |=> (count == 4'h0)
    );

endmodule
