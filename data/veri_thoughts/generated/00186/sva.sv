module counter_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] count
);

    // A sampled reset must leave the counter at zero on the next clock.
    check_sampled_reset_clears_count: assert property (
        @(posedge clk) disable iff ($initstate)
        rst |=> (count == 4'h0)
    );

    // The first sampled clock after reset deassertion still sees zero.
    check_reset_release_observes_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        $fell(rst) |-> (count == 4'h0)
    );

    // Outside reset, any nonzero count must be the previous count plus one.
    check_nonzero_count_increments_by_one: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (count != 4'h0) |-> (count == ($past(count) + 4'h1))
    );

    // Outside reset, a previous maximum count must wrap to zero.
    check_wrap_from_max_to_zero: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        ($past(count) == 4'hF) |-> (count == 4'h0)
    );

endmodule