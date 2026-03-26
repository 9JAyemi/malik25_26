module up_counter_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] count
);

    // Sequential 4-bit up-counter with asynchronous active-low reset.
    
    // A sampled reset cycle forces the next sampled count to zero.
    check_reset_drives_zero_next: assert property (
        @(posedge clk)
        !rst |=> (count == 4'h0)
    );

    // After a sampled low-to-high reset transition, count is still zero before incrementing.
    check_reset_release_starts_from_zero: assert property (
        @(posedge clk)
        (!rst ##1 rst) |-> (count == 4'h0)
    );

    // Below max, the next sampled count is either +1 or 0 if async reset intervenes.
    check_count_advances_or_resets: assert property (
        @(posedge clk) disable iff (!rst)
        (count != 4'hF) |=> ((count == ($past(count) + 4'd1)) || (count == 4'h0))
    );

    // At max, the 4-bit counter wraps to zero on the next sampled clock.
    check_count_wraps_from_max: assert property (
        @(posedge clk) disable iff (!rst)
        (count == 4'hF) |=> (count == 4'h0)
    );

    // From zero, the next sampled count is either 1 or 0 if async reset intervenes.
    check_zero_advances_or_resets: assert property (
        @(posedge clk) disable iff (!rst)
        (count == 4'h0) |=> ((count == 4'h1) || (count == 4'h0))
    );

endmodule