module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);

    // Reset forces the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |-> (count == 4'b0000)
    );

    // The first sampled cycle after reset release still shows zero.
    check_reset_release_starts_from_zero: assert property (
        @(posedge clk) disable iff (rst) $past(rst) |-> (count == 4'b0000)
    );

    // The counter increments by one on each non-reset cycle.
    check_count_increments: assert property (
        @(posedge clk) disable iff (rst) !rst |-> (count == ($past(count) + 4'd1))
    );

    // The 4-bit counter wraps from 15 back to 0.
    check_count_wraps_from_max: assert property (
        @(posedge clk) disable iff (rst) (!rst && (count == 4'hF)) |-> (count == 4'h0)
    );

endmodule