module constant_voltage_driver_sva #(
    parameter int unsigned voltage_level = 1800,
    parameter int unsigned rise_time     = 10,
    parameter int unsigned fall_time     = 20
) (
    input logic        clk,
    input logic        rst,
    input logic        ctrl,
    input logic        vout,
    input logic [31:0] rise_counter,
    input logic [31:0] fall_counter
);

    ///// Reset behavior /////
    // On reset assertion, next cycle vout and both counters are 0.
    reset_clears_state_next: assert property (
        @(posedge clk) rst |=> (vout == 1'b0) && (rise_counter == 32'd0) && (fall_counter == 32'd0)
    );

    // While reset remains asserted, state holds at 0.
    hold_zero_while_reset: assert property (
        @(posedge clk) rst && $past(rst) |-> (vout == 1'b0) && (rise_counter == 32'd0) && (fall_counter == 32'd0)
    );

    ///// Counter control /////
    // When ctrl is HIGH, fall_counter is forced to 0 next cycle.
    ctrl_high_forces_fall_zero_next: assert property (
        @(posedge clk) disable iff (rst) ctrl |-> ##1 (fall_counter == 32'd0)
    );

    // When ctrl is LOW, rise_counter is forced to 0 next cycle.
    ctrl_low_forces_rise_zero_next: assert property (
        @(posedge clk) disable iff (rst) !ctrl |-> ##1 (rise_counter == 32'd0)
    );

    ///// Rise counter behavior /////
    // With ctrl HIGH and below rise_time, rise_counter increments by 1.
    rise_increments_until_limit: assert property (
        @(posedge clk) disable iff (rst) ctrl && (rise_counter < rise_time) |=> (rise_counter == $past(rise_counter) + 32'd1)
    );

    // With ctrl HIGH and at/above rise_time, rise_counter holds.
    rise_holds_at_limit: assert property (
        @(posedge clk) disable iff (rst) ctrl && (rise_counter >= rise_time) |=> (rise_counter == $past(rise_counter))
    );

    // While ctrl stays HIGH, rise_counter is non-decreasing and steps by at most 1.
    rise_monotonic_while_ctrl_high: assert property (
        @(posedge clk) disable iff (rst) $past(ctrl) && ctrl |-> (rise_counter >= $past(rise_counter)) && (rise_counter <= $past(rise_counter) + 32'd1)
    );

    // Under ctrl HIGH, rise_counter never exceeds rise_time.
    rise_never_exceeds_limit: assert property (
        @(posedge clk) disable iff (rst) ctrl |-> (rise_counter <= rise_time)
    );

    ///// Fall counter behavior /////
    // With ctrl LOW and below fall_time, fall_counter increments by 1.
    fall_increments_until_limit: assert property (
        @(posedge clk) disable iff (rst) !ctrl && (fall_counter < fall_time) |=> (fall_counter == $past(fall_counter) + 32'd1)
    );

    // With ctrl LOW and at/above fall_time, fall_counter holds.
    fall_holds_at_limit: assert property (
        @(posedge clk) disable iff (rst) !ctrl && (fall_counter >= fall_time) |=> (fall_counter == $past(fall_counter))
    );

    // While ctrl stays LOW, fall_counter is non-decreasing and steps by at most 1.
    fall_monotonic_while_ctrl_low: assert property (
        @(posedge clk) disable iff (rst) !$past(ctrl) && !ctrl |-> (fall_counter >= $past(fall_counter)) && (fall_counter <= $past(fall_counter) + 32'd1)
    );

    // Under ctrl LOW, fall_counter never exceeds fall_time.
    fall_never_exceeds_limit: assert property (
        @(posedge clk) disable iff (rst) !ctrl |-> (fall_counter <= fall_time)
    );

    ///// vout stability in saturated regions /////
    // When rising has saturated (ctrl HIGH and previously at/above limit), vout is stable.
    vout_stable_when_rise_saturated: assert property (
        @(posedge clk) disable iff (rst) $past(ctrl) && ctrl && ($past(rise_counter) >= rise_time) |-> (vout == $past(vout))
    );

    // When falling has saturated (ctrl LOW and previously at/above limit), vout is stable.
    vout_stable_when_fall_saturated: assert property (
        @(posedge clk) disable iff (rst) !$past(ctrl) && !ctrl && ($past(fall_counter) >= fall_time) |-> (vout == $past(vout))
    );

endmodule