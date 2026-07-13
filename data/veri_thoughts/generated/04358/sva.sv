module binary_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] count
);

    // Count is zero whenever reset is asserted low.
    check_reset_clears_count: assert property (
        @(posedge clk) !reset |-> (count == 4'b0000)
    );

    // The first sampled cycle after reset release still shows zero.
    check_post_reset_starts_at_zero: assert property (
        @(posedge clk) disable iff (!reset)
        ($past(reset) === 1'b0) |-> (count == 4'b0000)
    );

    // On consecutive enabled cycles, count increments by one.
    check_count_increments: assert property (
        @(posedge clk) disable iff (!reset)
        ($past(reset) === 1'b1) |-> (count == ($past(count) + 4'b0001))
    );

    // The 4-bit counter wraps from 15 back to 0.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (!reset)
        (($past(reset) === 1'b1) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

endmodule