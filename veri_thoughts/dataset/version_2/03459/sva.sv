module binary_counter_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] count
);

    // Reset forces count to zero by the next clock sample.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 4'b0000)
    );

    // On reset release, the sampled count is still zero on that clock edge.
    check_reset_release_starts_from_zero: assert property (
        @(posedge clk) disable iff (rst)
        $fell(rst) |-> (count == 4'b0000)
    );

    // Without reset, count increments by one on each clock.
    check_count_increments: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (count == ($past(count) + 4'd1))
    );

    // A maximum count value wraps back to zero on the next clock.
    check_count_wraps_from_max: assert property (
        @(posedge clk) disable iff (rst)
        (count == 4'hf) |=> (count == 4'h0)
    );

endmodule