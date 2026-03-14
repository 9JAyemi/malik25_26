module binary_counter_4bit_sva (
    input logic clk,
    input logic rst_n,
    input logic [3:0] count
);

    // When reset is asserted low at a clock edge, count must be zero.
    reset_level_forces_zero: assert property (
        @(posedge clk) (!rst_n) |-> (count == 4'b0000)
    );

    // If reset is held low across consecutive clock edges, count remains zero.
    reset_held_keeps_zero: assert property (
        @(posedge clk) (!rst_n && $past(!rst_n)) |-> (count == 4'b0000)
    );

    // On a falling edge of rst_n (detected at the clock), count is zero.
    reset_fall_clears_count: assert property (
        @(posedge clk) $fell(rst_n) |-> (count == 4'b0000)
    );

    // On reset deassertion (rising edge of rst_n sampled at the clock), count becomes 1.
    reset_release_sets_one: assert property (
        @(posedge clk) $rose(rst_n) |-> (count == 4'b0001)
    );

    // In non-reset cycles, next value is either prior+1 (mod 16) or 1 if an async reset occurred between clocks.
    next_value_inc_or_one: assert property (
        @(posedge clk) disable iff (!rst_n)
            (count == (($past(count) + 4'd1) & 4'hF)) || (count == 4'h1)
    );

    // In non-reset cycles, observing count==0 implies prior sample was 15 (wrap event).
    zero_only_from_wrap: assert property (
        @(posedge clk) disable iff (!rst_n)
            (count == 4'h0) |-> ($past(count) == 4'hF)
    );

endmodule