module configurable_counter_sva (
    input logic clk,
    input logic reset,           // active-high async reset
    input logic [7:0] max_count,
    input logic [7:0] count
);

    // Reset forces count to zero whenever sampled high on clk.
    check_reset_forces_zero: assert property (
        @(posedge clk) reset |-> (count == 8'd0)
    );

    // Next-state function: on the next cycle, either reset is asserted or count updates per RTL (uses current max_count and previous count).
    check_next_state_matches_rtl: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |-> ##1 (reset || (count == (($past(count) == max_count) ? 8'd0 : ($past(count) + 8'd1))))
    );

    // If previous count equals current max_count, next count is zero.
    check_wrap_when_prev_eq_current_max: assert property (
        @(posedge clk) disable iff (reset)
        ($past(count) == max_count) |-> (count == 8'd0)
    );

    // If previous count does not equal current max_count, next count increments by one (mod 256).
    check_increment_when_prev_not_equal: assert property (
        @(posedge clk) disable iff (reset)
        ($past(count) != max_count) |-> (count == ($past(count) + 8'd1))
    );

    // On every non-reset cycle, next count is either zero or previous+1.
    check_zero_or_plus1_transition: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |-> ##1 (reset || (count == 8'd0) || (count == ($past(count) + 8'd1)))
    );

    // If not in reset and next count is zero, then previous count was max_count or 8'hFF (wrap via +1).
    check_zero_implies_prev_eq_max_or_prev_ff: assert property (
        @(posedge clk) disable iff (reset)
        (count == 8'd0) |-> (($past(count) == max_count) || ($past(count) == 8'hFF))
    );

    // On reset deassertion, count becomes 0 (if max_count==0) or 1 (otherwise) at that clk edge.
    check_reset_deassertion_result: assert property (
        @(posedge clk) $fell(reset) |-> (count == 8'd0 || count == 8'd1)
    );

endmodule