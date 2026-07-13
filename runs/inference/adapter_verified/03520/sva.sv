module counter_sva (
    input logic clk,
    input logic rst,
    input logic [7:0] count
);

// Reset drives count to zero on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 8'h00)
    );

// When not in reset, count increments by one on the next clock.
    check_count_increments: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (count == ($past(count) + 8'd1))
    );

// Count wraps from 255 back to 0 when not in reset.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (rst) (count == 8'hFF) |=> (count == 8'h00)
    );

endmodule
