module binary_counter_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] count
);

    // While reset is asserted, the counter output must be zero.
    check_reset_holds_zero: assert property (
        @(posedge clk) rst |-> (count == 4'h0)
    );

    // On the first sampled cycle after reset deasserts, the counter is still zero.
    check_reset_deassert_sample_zero: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        $fell(rst) |-> (count == 4'h0)
    );

    // A previous value of 4'hF always appears as 4'h0 on the next sampled non-reset cycle.
    check_wrap_from_max_to_zero: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

    // From any other previous value, the next sampled non-reset value is either +1 or 0 from async reset.
    check_nonwrap_next_or_async_reset_zero: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && ($past(count) != 4'hF))
        |-> ((count == ($past(count) + 4'd1)) || (count == 4'h0))
    );

    // Any nonzero sampled count on a non-reset cycle must come from the prior value incrementing by one.
    check_nonzero_count_matches_increment: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && (count != 4'h0)) |-> (count == ($past(count) + 4'd1))
    );

endmodule