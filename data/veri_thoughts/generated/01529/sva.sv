module up_counter_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] count
);
    // On any cycle with reset asserted, count is driven to 0.
    reset_drives_zero: assert property (
        @(posedge clk) reset |-> (count == 4'd0)
    );

    // When not in reset for consecutive cycles, count increments by 1 (mod 16).
    count_increments_no_reset: assert property (
        @(posedge clk) disable iff (reset)
        $past(!reset) |-> (count == $past(count) + 4'd1)
    );

    // If previous count was 15 and still not in reset, count wraps to 0.
    count_wraps_from_max: assert property (
        @(posedge clk) disable iff (reset)
        ($past(!reset) && ($past(count) == 4'hF)) |-> (count == 4'd0)
    );

    // On the cycle after reset deasserts, count becomes 1.
    count_one_after_reset_deassert: assert property (
        @(posedge clk) disable iff (reset)
        ($past(reset) && !reset) |-> (count == 4'd1)
    );

    // If count is 0 on a non-reset cycle following a non-reset cycle, it wrapped from 15.
    zero_implies_prev_max: assert property (
        @(posedge clk) disable iff (reset)
        ($past(!reset) && !reset && (count == 4'd0)) |-> ($past(count) == 4'hF)
    );

    // LSB toggles on each non-reset cycle (increment by 1).
    lsb_toggles_each_step: assert property (
        @(posedge clk) disable iff (reset)
        $past(!reset) |-> (count[0] == ~$past(count[0]))
    );
endmodule