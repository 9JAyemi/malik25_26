module touch_sensor_interface_assertions (
    input logic proximity_signal,
    input logic clk,
    input logic proximity_event,
    input logic [7:0] proximity_position
);

    // A sampled high input sets the event output on the next cycle.
    check_event_asserts_after_high_input: assert property (
        @(posedge clk) proximity_signal |=> (proximity_event == 1'b1)
    );

    // A sampled low input clears the event output on the next cycle.
    check_event_clears_after_low_input: assert property (
        @(posedge clk) !proximity_signal |=> (proximity_event == 1'b0)
    );

    // The reported position is driven to zero after every clock update.
    check_position_forced_zero: assert property (
        @(posedge clk) 1'b1 |=> (proximity_position == 8'h00)
    );

endmodule