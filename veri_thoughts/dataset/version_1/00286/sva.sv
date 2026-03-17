module counter_module_sva #(
    parameter int unsigned max_count = 255
) (
    input logic       clk,
    input logic       reset,
    input logic [7:0] count
);

    // Count either increments or returns to zero on each active clock.
    check_count_step_or_zero: assert property (
        @(posedge clk) disable iff (reset)
        !$initstate |-> ((count == 8'd0) || (count == ($past(count) + 8'd1)))
    );

    // A sampled max_count value wraps to zero on the next active clock.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && ($past(count) == max_count)) |-> (count == 8'd0)
    );

    // Any nonzero count must come from incrementing the previous sampled value.
    check_nonzero_is_increment: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && (count != 8'd0)) |-> (!$past(reset) && (count == ($past(count) + 8'd1)))
    );

    // The first active clock after a sampled reset still shows zero.
    check_post_reset_zero: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(reset)) |-> (count == 8'd0)
    );

    // Once the count is in range, the next sampled count stays in range.
    check_range_invariant: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && ($past(count) <= max_count)) |-> (count <= max_count)
    );

endmodule