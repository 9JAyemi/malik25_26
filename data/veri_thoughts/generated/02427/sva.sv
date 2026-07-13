module counter_sva (
    input logic clk,
    input logic rst,           // active-low reset
    input logic [3:0] count
);
    // While reset is asserted (low), count is 0 at each clock.
    check_reset_forces_zero: assert property (
        @(posedge clk) (rst == 1'b0) |-> (count == 4'd0)
    );

    // On reset assertion (1->0), count is 0 at that clock.
    check_zero_on_reset_assert: assert property (
        @(posedge clk) $fell(rst) |-> (count == 4'd0)
    );

    // On reset deassertion (0->1), next count becomes 1 (after 0).
    check_one_on_reset_release: assert property (
        @(posedge clk) $rose(rst) |-> (count == 4'd1) && ($past(count) == 4'd0)
    );

    // In run (rst=1), if count is 0 then previous must have been 15 (wrap).
    check_wrap_from_fifteen_only: assert property (
        @(posedge clk) disable iff (!rst) (count == 4'd0) |-> ($past(count) == 4'd15)
    );

    // In run (rst=1), for any count != 1, previous equals current-1 (mod 16).
    check_prev_matches_curr_minus_one: assert property (
        @(posedge clk) disable iff (!rst) (count != 4'd1) |-> ($past(count) == (count - 4'd1))
    );

    // If count is non-zero at a clock, reset must be deasserted.
    check_nonzero_implies_not_in_reset: assert property (
        @(posedge clk) (count != 4'd0) |-> (rst == 1'b1)
    );

    // If reset is held low across consecutive clocks, count stays 0.
    check_sticky_zero_during_reset: assert property (
        @(posedge clk) (!rst && $past(!rst)) |-> (count == 4'd0 && $past(count) == 4'd0)
    );
endmodule