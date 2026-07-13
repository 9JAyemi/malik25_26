module sensor_interface_sva (
    input logic clk,
    input logic reset,
    input logic [11:0] sensor_signal,
    input logic [15:0] output_signal
);
    // Synchronous reset drives output_signal to zero on the next cycle.
    reset_clears_output_next: assert property (
        @(posedge clk) reset |=> (output_signal == 16'h0000)
    );

    // When not in reset, upper nibble is always zero.
    high_nibble_zero_when_running: assert property (
        @(posedge clk) disable iff (reset) (output_signal[15:12] == 4'b0000)
    );

    // When previous cycle not in reset, full output equals {0, previous sensor}.
    output_maps_prev_sensor: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) |-> (output_signal == {4'b0000, $past(sensor_signal)}))
    );

    // On the cycle after reset was high, output is zero.
    post_reset_output_zero: assert property (
        @(posedge clk) disable iff (reset) ($past(reset) |-> (output_signal == 16'h0000))
    );

    // If sensor held same value for two cycles (no reset), output holds its value.
    output_holds_when_sensor_stable: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && !$past(reset,2) && ($past(sensor_signal) == $past(sensor_signal,2))) |-> (output_signal == $past(output_signal))
    );
endmodule