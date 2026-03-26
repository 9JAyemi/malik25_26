module binary_counter_assertions (
    input logic        clk,
    input logic        reset,
    input logic [31:0] max_count,
    input logic [31:0] count
);

    // Sequential counter on clk with active-high reset.
    
    // Reset forces count to zero at any sampled clock edge.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |-> (count == 32'd0)
    );

    // A sampled reset leaves count at zero until the next sampled edge.
    check_reset_holds_zero_to_next_sample: assert property (
        @(posedge clk) reset |=> (count == 32'd0)
    );

    // Reaching max_count wraps the counter to zero on the next sample.
    check_wraps_to_zero_at_max: assert property (
        @(posedge clk) disable iff (reset)
        (count == max_count) |=> (count == 32'd0)
    );

    // An all-ones count returns to zero on the next sample.
    check_all_ones_wraps_to_zero: assert property (
        @(posedge clk) disable iff (reset)
        (count == 32'hFFFF_FFFF) |=> (count == 32'd0)
    );

    // Each non-reset update is either +1 or a reset/wrap to zero.
    check_update_is_increment_or_zero: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> ((count == 32'd0) || (count == ($past(count) + 32'd1)))
    );

    // From zero, the next sampled value can only stay zero or move to one.
    check_zero_moves_to_zero_or_one: assert property (
        @(posedge clk) disable iff (reset)
        (count == 32'd0) |=> ((count == 32'd0) || (count == 32'd1))
    );

    // With count and max_count both zero, zero is retained on the next sample.
    check_zero_max_keeps_zero: assert property (
        @(posedge clk) disable iff (reset)
        ((count == 32'd0) && (max_count == 32'd0)) |=> (count == 32'd0)
    );

endmodule