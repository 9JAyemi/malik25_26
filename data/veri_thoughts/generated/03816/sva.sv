module binary_counter_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] count
);

    // A sampled reset drives the counter to zero by the next clock.
    reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 4'd0)
    );

    // A count of 9 rolls over to 0 on the next clock.
    count_rolls_over_at_nine: assert property (
        @(posedge clk) disable iff (reset)
            (count == 4'd9) |=> (count == 4'd0)
    );

    // Any non-9 count advances by one, or is forced to 0 by async reset.
    count_advances_or_resets_otherwise: assert property (
        @(posedge clk) disable iff (reset)
            (count != 4'd9) |=> ((count == ($past(count) + 4'd1)) || (count == 4'd0))
    );

endmodule