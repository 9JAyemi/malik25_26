module binary_counter_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] count
);

// Reset drives count to zero on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 4'b0000)
    );

// When not in reset, count increments by one each cycle.
    check_count_increments: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (count == ($past(count) + 4'd1))
    );

// Count wraps from 15 back to 0 when not in reset.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (rst) (count == 4'hF) |=> (count == 4'h0)
    );

endmodule
