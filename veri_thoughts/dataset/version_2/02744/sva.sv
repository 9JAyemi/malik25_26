module counter_4bit_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);
    // When reset is asserted at a clock edge, count must be 0.
    check_reset_clears: assert property (
        @(posedge clk) rst |-> (count == 4'd0)
    );

    // While reset remains asserted across consecutive clock edges, count stays 0.
    check_reset_holds_zero: assert property (
        @(posedge clk) (rst && $past(rst)) |-> (count == 4'd0) && ($past(count) == 4'd0)
    );

    // On the sampled rising edge of reset, count is 0.
    check_reset_assert_edge_clears: assert property (
        @(posedge clk) $rose(rst) |-> (count == 4'd0)
    );

    // Just before reset deasserts, count was 0 (due to reset).
    check_prev_zero_before_release: assert property (
        @(posedge clk) disable iff (rst) $fell(rst) |-> ($past(count) == 4'd0)
    );

    // On the first clock after reset deassertion, count increments to 1.
    check_first_increment_after_release: assert property (
        @(posedge clk) disable iff (rst) $fell(rst) |-> (count == 4'd1)
    );
endmodule