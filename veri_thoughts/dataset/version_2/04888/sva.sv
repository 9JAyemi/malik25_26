module counter_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] count
);

    // When reset is sampled high, count must be zero.
    reset_holds_count_zero: assert property (
        @(posedge clk)
        rst |-> (count == 4'b0000)
    );

    // A sampled reset keeps count at zero on the next sampled cycle.
    reset_keeps_next_count_zero: assert property (
        @(posedge clk)
        rst |=> (count == 4'b0000)
    );

    // Between sampled clocks, count can only increment or be cleared by async reset.
    count_next_is_zero_or_incremented: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> ((count == 4'b0000) || (count == ($past(count) + 4'd1)))
    );

    // A sampled max count must wrap to zero on the next sampled active cycle.
    count_wraps_after_max: assert property (
        @(posedge clk) disable iff (rst)
        (count == 4'hF) |=> (count == 4'h0)
    );

endmodule