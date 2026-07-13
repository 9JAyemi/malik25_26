module counter_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] count
);

    // Reset drives count to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) (!rst) |-> (count == 4'd0)
    );

    // When count is below 15, it increments by one on the next clock.
    check_count_increments: assert property (
        @(posedge clk) disable iff (!rst)
        (count != 4'hF) |=> (count == ($past(count) + 4'd1))
    );

    // When count reaches 15, it wraps to zero on the next clock.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (!rst)
        (count == 4'hF) |=> (count == 4'h0)
    );

endmodule