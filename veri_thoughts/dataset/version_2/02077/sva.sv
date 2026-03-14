module clock_counter_sva (
    input  logic        clk_i,
    input  logic        reset_n,
    input  logic        clk_o,
    input  logic [15:0] count
);
    // Clock: clk_i (posedge). Reset: reset_n (active-low async). Sequential counter toggles clk_o when count >= 17333.

    // Under reset, clk_o and count are driven LOW/zero.
    check_reset_forces_low: assert property (
        @(posedge clk_i) !reset_n |-> (clk_o == 1'b0) && (count == 16'd0)
    );

    // On reset deassertion, first active cycle keeps clk_o low and sets count to 1.
    check_reset_release_first_cycle: assert property (
        @(posedge clk_i) $rose(reset_n) |-> (clk_o == 1'b0) && (count == 16'd1)
    );

    // When previously below threshold, count increments by 1 and clk_o holds.
    check_increment_below_threshold: assert property (
        @(posedge clk_i) disable iff (!reset_n)
            $past(reset_n) && ($past(count) < 16'd17333)
            |-> (count == $past(count) + 16'd1) && (clk_o == $past(clk_o))
    );

    // When previously at/above threshold, clk_o toggles and count clears to 0.
    check_toggle_and_clear_at_threshold: assert property (
        @(posedge clk_i) disable iff (!reset_n)
            $past(reset_n) && ($past(count) >= 16'd17333)
            |-> (clk_o == ~$past(clk_o)) && (count == 16'd0)
    );

    // clk_o must not toggle when previously below threshold.
    check_no_toggle_below_threshold: assert property (
        @(posedge clk_i) disable iff (!reset_n)
            $past(reset_n) && ($past(count) < 16'd17333)
            |-> $stable(clk_o)
    );

    // Any clk_o toggle in run state must be caused by previously reaching threshold.
    check_toggle_only_when_threshold: assert property (
        @(posedge clk_i) disable iff (!reset_n)
            $changed(clk_o) |-> ($past(reset_n) && ($past(count) >= 16'd17333))
    );

    // No back-to-back clk_o toggles on consecutive active cycles.
    check_no_back_to_back_toggles: assert property (
        @(posedge clk_i) disable iff (!reset_n)
            $changed(clk_o) |-> ##1 (reset_n && $stable(clk_o))
    );

    // In run state, count == 0 can only occur after previously reaching threshold.
    check_zero_count_only_from_threshold: assert property (
        @(posedge clk_i) disable iff (!reset_n)
            (count == 16'd0 && $past(reset_n)) |-> ($past(count) >= 16'd17333)
    );

    // In run state, count is always bounded by the threshold.
    check_count_bounded_running: assert property (
        @(posedge clk_i) disable iff (!reset_n)
            $past(reset_n) |-> (count <= 16'd17333)
    );

    // After a toggle/clear cycle, next active cycle sets count to 1 and holds clk_o.
    check_post_toggle_next_cycle: assert property (
        @(posedge clk_i) disable iff (!reset_n)
            $past(reset_n) && ($past(count) >= 16'd17333)
            |-> ##1 (reset_n && (count == 16'd1) && $stable(clk_o))
    );

endmodule