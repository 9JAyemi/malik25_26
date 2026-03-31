module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic [2:0] count
);

// Reset low forces count to 0 on the next sampled cycle.
    check_reset_clears_count: assert property (
        @(posedge clk) !rst |=> (count == 3'b000)
    );

// When not in reset, count increments by 1 on the next sampled cycle.
    check_count_increments: assert property (
        @(posedge clk) disable iff (!rst) 1'b1 |=> (count == ($past(count) + 3'd1))
    );

// Count wraps from 7 back to 0 when not in reset.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (!rst) (count == 3'b111) |=> (count == 3'b000)
    );

endmodule
