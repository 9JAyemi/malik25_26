module binary_counter_sva(
    input logic clk,
    input logic rst,
    input logic [3:0] count
);

    // A reset cycle clears the counter for the following sampled cycle.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 4'd0)
    );

    // The first non-reset cycle after reset still observes count at zero.
    check_reset_release_shows_zero: assert property (
        @(posedge clk) disable iff (rst) (($past(rst) === 1'b1)) |-> (count == 4'd0)
    );

    // When below 15 and not in reset, the counter increments by one.
    check_increment_when_below_max: assert property (
        @(posedge clk) disable iff (rst) (count < 4'd15) |=> (count == ($past(count) + 4'd1))
    );

    // When at 15 and not in reset, the counter wraps to zero.
    check_wrap_from_max_to_zero: assert property (
        @(posedge clk) disable iff (rst) (count == 4'd15) |=> (count == 4'd0)
    );

endmodule