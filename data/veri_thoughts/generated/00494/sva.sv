module up_counter_sva(
    input logic clk,
    input logic rst,
    input logic [3:0] count
);

    // Reset drives count to zero on the following cycle.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 4'd0)
    );

    // If reset remains asserted, count stays at zero.
    check_reset_holds_zero: assert property (
        @(posedge clk) rst |=> (rst -> (count == 4'd0))
    );

    // After reset deasserts, the first sampled count is zero.
    check_reset_release_starts_from_zero: assert property (
        @(posedge clk) rst |=> (!rst -> (count == 4'd0))
    );

    // Across consecutive non-reset cycles, count increments by one.
    check_count_increments: assert property (
        @(posedge clk) disable iff (rst) !rst |=> (count == ($past(count) + 4'd1))
    );

    // The 4-bit counter wraps from 15 back to 0.
    check_count_rollover: assert property (
        @(posedge clk) disable iff (rst) (!rst && (count == 4'hf)) |=> (count == 4'h0)
    );

endmodule