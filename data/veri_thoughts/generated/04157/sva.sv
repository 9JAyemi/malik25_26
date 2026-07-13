module counter_4bit_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] count
);

    // A reset cycle leaves the counter at zero on the next sampled cycle.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 4'b0000)
    );

    // The first sampled cycle after reset deassertion still sees zero.
    check_reset_release_starts_at_zero: assert property (
        @(posedge clk) (rst ##1 !rst) |-> (count == 4'b0000)
    );

    // After reset deasserts and one running cycle passes, count becomes one.
    check_reset_release_then_increment: assert property (
        @(posedge clk) (rst ##1 !rst ##1 !rst) |-> (count == 4'b0001)
    );

    // When not in reset, the counter increments by one each clock.
    check_count_increments_by_one: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (count == ($past(count) + 4'b0001))
    );

    // The 4-bit counter wraps from 15 back to 0.
    check_count_wraps_from_f_to_0: assert property (
        @(posedge clk) disable iff (rst) (count == 4'hF) |=> (count == 4'h0)
    );

endmodule