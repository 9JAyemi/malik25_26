module touch_sensor_interface_sva #(
    parameter int sensor_type = 0,
    parameter int threshold   = 64
) (
    input logic        touch_signal,
    input logic        touch_detected,
    input logic [31:0] rc_time_constant,
    input logic [7:0]  adc_value
);

    // RC time constant increments on every touch_signal rising edge.
    check_rc_time_constant_increments: assert property (
        @(posedge touch_signal) 1'b1 |=> rc_time_constant == ($past(rc_time_constant) + 32'd1)
    );

    // ADC value holds when resistive mode is not selected.
    check_adc_value_holds_when_not_resistive: assert property (
        @(posedge touch_signal) sensor_type != 1 |=> adc_value == $past(adc_value)
    );

    // Resistive mode loads the ADC value to full scale.
    check_adc_value_loads_full_scale_in_resistive: assert property (
        @(posedge touch_signal) sensor_type == 1 |=> adc_value == 8'hFF
    );

    // Capacitive mode drives touch_detected from the prior RC comparison.
    check_touch_detected_from_rc_threshold: assert property (
        @(posedge touch_signal) sensor_type == 0 |=> touch_detected == ($past(rc_time_constant) > threshold)
    );

    // Resistive mode drives touch_detected from the prior ADC comparison.
    check_touch_detected_from_adc_threshold: assert property (
        @(posedge touch_signal) sensor_type == 1 |=> touch_detected == ($past(adc_value) > threshold)
    );

    // Unsupported sensor_type values leave touch_detected unchanged.
    check_touch_detected_holds_for_invalid_mode: assert property (
        @(posedge touch_signal) (sensor_type != 0) && (sensor_type != 1) |=> touch_detected == $past(touch_detected)
    );

endmodule