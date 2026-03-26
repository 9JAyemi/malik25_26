module binary_up_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic       enable,
    input logic [3:0] count
);

    // Reset clears the counter on the next sampled clock.
    check_reset_clears_count: assert property (
        @(posedge clk) disable iff ($initstate)
        reset |=> (count == 4'd0)
    );

    // Reset overrides enable and still clears the counter.
    check_reset_priority_over_enable: assert property (
        @(posedge clk) disable iff ($initstate)
        reset && enable |=> (count == 4'd0)
    );

    // When disabled and not in reset, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff ($initstate)
        !reset && !enable |=> (count == $past(count))
    );

    // When enabled below 15, the counter increments by one.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff ($initstate)
        !reset && enable && (count != 4'd15) |=> (count == ($past(count) + 4'd1))
    );

    // When enabled at 15, the counter wraps back to zero.
    check_wrap_at_max: assert property (
        @(posedge clk) disable iff ($initstate)
        !reset && enable && (count == 4'd15) |=> (count == 4'd0)
    );

    // Every sampled count matches the RTL next-state function.
    check_count_follows_rtl_transition: assert property (
        @(posedge clk) disable iff ($initstate)
        1'b1 |=> (count == ($past(reset) ? 4'd0 :
                            ($past(enable) ? (($past(count) == 4'd15) ? 4'd0 : ($past(count) + 4'd1))
                                           : $past(count))))
    );

endmodule