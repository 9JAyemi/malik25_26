module binary_counter_assertions (
    input logic       clk,
    input logic       rst,
    input logic [3:0] count
);

    // Reset forces the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) disable iff ($initstate) rst |-> (count == 4'b0000)
    );

    // The first clock after reset release still observes zero before incrementing.
    check_reset_release_starts_from_zero: assert property (
        @(posedge clk) disable iff (rst || $initstate) $past(rst) |-> (count == 4'b0000)
    );

    // In normal operation, the counter increments by one every clock.
    check_count_increments_each_cycle: assert property (
        @(posedge clk) disable iff (rst || $initstate) !$past(rst) |-> (count == ($past(count) + 4'd1))
    );

    // A count of 15 wraps back to 0 on the next active clock.
    check_count_wraps_from_f_to_zero: assert property (
        @(posedge clk) disable iff (rst || $initstate) (!$past(rst) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

endmodule