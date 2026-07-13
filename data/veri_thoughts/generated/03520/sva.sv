module counter_sva (
    input logic       clk,
    input logic       rst,
    input logic [7:0] count
);

    // A sampled reset must force count to zero by the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 8'h00)
    );

    // The first sampled cycle after reset release still shows zero.
    check_post_reset_count_zero: assert property (
        @(posedge clk) disable iff (rst)
        (!$initstate && $past(rst)) |-> (count == 8'h00)
    );

    // Outside reset, each sampled count is either zero or the previous count plus one.
    check_count_is_zero_or_increments: assert property (
        @(posedge clk) disable iff (rst)
        (!$initstate) |-> ((count == 8'h00) || (count == ($past(count) + 8'd1)))
    );

    // A previous value of 8'hFF must wrap to 8'h00 on the next sampled active clock.
    check_count_wraps_at_max: assert property (
        @(posedge clk) disable iff (rst)
        (!$initstate && ($past(count) == 8'hFF)) |-> (count == 8'h00)
    );

endmodule