module digital_clock_sva (
    input logic       clk,
    input logic       reset,
    input logic [5:0] sec,
    input logic [5:0] min,
    input logic [4:0] hr,
    input logic       ampm
);

    // Reset drives the observable clock state to 00:00:12 AM by the next sampled cycle.
    check_reset_state: assert property (
        @(posedge clk) reset |=> (sec == 6'd0 && min == 6'd0 && hr == 5'd12 && ampm == 1'b0)
    );

    // Seconds stay within the implemented 0 to 49 range.
    check_sec_range: assert property (
        @(posedge clk) disable iff (reset) sec <= 6'd49
    );

    // Minutes stay within the implemented 0 to 59 range.
    check_min_range: assert property (
        @(posedge clk) disable iff (reset) min <= 6'd59
    );

    // Hours are always presented as 1 through 12.
    check_hr_range: assert property (
        @(posedge clk) disable iff (reset) (hr >= 5'd1) && (hr <= 5'd12)
    );

    // When seconds have not wrapped, only seconds increment.
    check_second_increment: assert property (
        @(posedge clk) disable iff (reset)
        (sec < 6'd49) |=> (sec == ($past(sec) + 6'd1) &&
                           min == $past(min) &&
                           hr == $past(hr) &&
                           ampm == $past(ampm))
    );

    // At second wrap, minutes increment and hours/AMPM hold when minutes have not wrapped.
    check_minute_increment: assert property (
        @(posedge clk) disable iff (reset)
        (sec == 6'd49 && min < 6'd59) |=> (sec == 6'd0 &&
                                           min == ($past(min) + 6'd1) &&
                                           hr == $past(hr) &&
                                           ampm == $past(ampm))
    );

    // At 12:59:49, the next hour becomes 1 and AM/PM does not change.
    check_hour_increment_from_12: assert property (
        @(posedge clk) disable iff (reset)
        (sec == 6'd49 && min == 6'd59 && hr == 5'd12) |=> (sec == 6'd0 &&
                                                            min == 6'd0 &&
                                                            hr == 5'd1 &&
                                                            ampm == $past(ampm))
    );

    // At 1 through 10 with full rollover, the hour increments by one and AM/PM holds.
    check_hour_increment_midrange: assert property (
        @(posedge clk) disable iff (reset)
        (sec == 6'd49 && min == 6'd59 && hr >= 5'd1 && hr <= 5'd10) |=> (sec == 6'd0 &&
                                                                           min == 6'd0 &&
                                                                           hr == ($past(hr) + 5'd1) &&
                                                                           ampm == $past(ampm))
    );

    // At 11:59:49, the next hour becomes 12 and AM/PM toggles.
    check_hour_rollover_toggles_ampm: assert property (
        @(posedge clk) disable iff (reset)
        (sec == 6'd49 && min == 6'd59 && hr == 5'd11) |=> (sec == 6'd0 &&
                                                            min == 6'd0 &&
                                                            hr == 5'd12 &&
                                                            ampm == !$past(ampm))
    );

endmodule