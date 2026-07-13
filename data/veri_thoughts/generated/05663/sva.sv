module binary_counter_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] count
);

    // Reset restarts the counter at zero.
    check_post_reset_zero: assert property (
        @(posedge clk) disable iff (rst)
        !$initstate && $past(rst) |-> (count == 4'h0)
    );

    // Counts below 15 increment by one each cycle.
    check_increment_from_non_max: assert property (
        @(posedge clk) disable iff (rst)
        !$initstate && !$past(rst) && ($past(count) != 4'hF) |-> (count == ($past(count) + 4'h1))
    );

    // Count 15 wraps back to zero.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (rst)
        !$initstate && !$past(rst) && ($past(count) == 4'hF) |-> (count == 4'h0)
    );

    // Zero can only result from reset or wraparound.
    check_zero_origin: assert property (
        @(posedge clk) disable iff (rst)
        !$initstate && (count == 4'h0) |-> ($past(rst) || ($past(count) == 4'hF))
    );

    // Any non-zero value comes from incrementing the prior count.
    check_nonzero_origin: assert property (
        @(posedge clk) disable iff (rst)
        !$initstate && (count != 4'h0) |-> (!$past(rst) && (count == ($past(count) + 4'h1)))
    );

endmodule