module alarm_system_sva (
    input logic [7:0] sensor_bus,
    input logic reset,     // synchronous, active-high
    input logic clk,
    input logic alarm,
    input logic [7:0] sensor_state
);
    // On a reset cycle, sensor_state clears to 0 on the next cycle.
    reset_clears_sensor_state_next: assert property (
        @(posedge clk) reset |=> (sensor_state == 8'h00)
    );

    // On a reset cycle, alarm clears to 0 on the next cycle.
    reset_clears_alarm_next: assert property (
        @(posedge clk) reset |=> (alarm == 1'b0)
    );

    // When not in reset, sensor_state samples sensor_bus on the next cycle.
    sensor_state_captures_bus_next_no_reset: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (sensor_state == $past(sensor_bus))
    );

    // When not in reset, alarm updates next cycle from sensor_state != 0.
    alarm_updates_from_sensor_state_next_no_reset: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (alarm == (sensor_state != 8'h00))
    );

    // If sensor_state is zero, alarm is low the next cycle (when not in reset).
    alarm_low_next_when_state_zero: assert property (
        @(posedge clk) disable iff (reset) (sensor_state == 8'h00) |=> (alarm == 1'b0)
    );

    // If any sensor_state bit is set, alarm is high the next cycle (when not in reset).
    alarm_high_next_when_state_nonzero: assert property (
        @(posedge clk) disable iff (reset) (sensor_state != 8'h00) |=> (alarm == 1'b1)
    );

    // With two consecutive non-reset cycles, alarm equals prior cycle's (sensor_bus != 0).
    alarm_matches_prev_bus_when_no_reset_2cycles: assert property (
        @(posedge clk) disable iff (reset) (!reset |=> (!reset && (alarm == ($past(sensor_bus) != 8'h00))))
    );

    // Immediately after reset deasserts, alarm must be 0 on that first non-reset cycle.
    alarm_zero_immediately_after_reset_release: assert property (
        @(posedge clk) reset ##1 (!reset) |-> (alarm == 1'b0)
    );

    // While reset is held across consecutive cycles, both registers read as 0.
    hold_zero_while_reset_held: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (sensor_state == 8'h00 && alarm == 1'b0)
    );
endmodule