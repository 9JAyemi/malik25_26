module counter_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] count
);

    // A sampled reset must leave the counter at zero by the next clock sample.
    reset_forces_zero_next_sample: assert property (
        @(posedge clk) disable iff ($initstate)
        rst |=> (count == 4'h0)
    );

    // After a sampled reset cycle, the next non-reset sample must still see zero.
    post_reset_sample_is_zero: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        $past(rst) |-> (count == 4'h0)
    );

    // Between clock samples, the counter can only stay at zero from reset or increment by one.
    count_is_zero_or_incremented: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        ((count == 4'h0) || (count == ($past(count) + 4'h1)))
    );

    // A sampled count of 1 must come from a sampled count of 0.
    one_has_zero_predecessor: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (count == 4'h1) |-> ($past(count) == 4'h0)
    );

    // A sampled count of 15 must come from a sampled count of 14.
    fifteen_has_fourteen_predecessor: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (count == 4'hF) |-> ($past(count) == 4'hE)
    );

    // A sampled count of 15 must wrap to zero by the next clock sample.
    max_count_wraps_to_zero: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        ($past(count) == 4'hF) |-> (count == 4'h0)
    );

endmodule