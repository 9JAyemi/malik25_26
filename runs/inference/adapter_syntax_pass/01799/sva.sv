module counter_4bit_async_reset_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);

    // Active-low reset forces the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) !rst |-> (count == 4'h0)
    );

    // The first sampled cycle after reset release still sees zero.
    check_release_from_reset_starts_at_zero: assert property (
        @(posedge clk) disable iff (!rst) $rose(rst) |-> (count == 4'h0)
    );

    // Below 15, the counter increments by one on each clock.
    check_count_increments_below_max: assert property (
        @(posedge clk) disable iff (!rst) (count != 4'hF) |=> (count == ($past(count) + 4'd1))
    );

    // At 15, the counter wraps back to zero.
    check_count_wraps_from_max: assert property (
        @(posedge clk) disable iff (!rst) (count == 4'hF) |=> (count == 4'h0)
    );

endmodule