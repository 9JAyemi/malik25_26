module sync_reset_counter_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] count
);

// A sampled reset cycle leaves count at zero on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) !rst |=> (count == 4'h0)
    );

// When not in reset, count increments by one on the next clock.
    check_count_increments: assert property (
        @(posedge clk) disable iff (!rst) 1'b1 |=> (count == ($past(count) + 4'd1))
    );

// The 4-bit counter wraps from 15 back to 0.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (!rst) (count == 4'hF) |=> (count == 4'h0)
    );

endmodule
