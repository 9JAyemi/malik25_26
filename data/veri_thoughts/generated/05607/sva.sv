module Touch_Sensor_Interface_sva #(
    parameter int ADC_RESOLUTION = 10,
    parameter int TOUCH_THRESHOLD = 512
) (
    input  logic touch_signal,
    input  logic clk,
    input  logic touch_detected,
    input  logic [15:0] filtered_signal,
    input  logic [ADC_RESOLUTION-1:0] adc_value
);

    // filtered_signal follows the implemented low-pass update each clock.
    check_filtered_signal_update: assert property (
        @(posedge clk)
        1'b1 |=> filtered_signal == $past(filtered_signal + ((touch_signal - filtered_signal) >> 4))
    );

    // adc_value captures the shifted prior filtered_signal each clock.
    check_adc_value_update: assert property (
        @(posedge clk)
        1'b1 |=> adc_value == ($past(filtered_signal) >> (16 - ADC_RESOLUTION))
    );

    // touch_detected is the threshold comparison of adc_value.
    check_touch_detected_compare: assert property (
        @(posedge clk)
        touch_detected == (adc_value > TOUCH_THRESHOLD)
    );

    // Equality to the threshold must not assert touch_detected.
    check_threshold_equality_not_detected: assert property (
        @(posedge clk)
        (adc_value == TOUCH_THRESHOLD) |-> !touch_detected
    );

    // The prior filtered_signal determines the next sampled touch_detected value.
    check_filtered_signal_to_touch_detected_latency: assert property (
        @(posedge clk)
        1'b1 |=> touch_detected == (($past(filtered_signal) >> (16 - ADC_RESOLUTION)) > TOUCH_THRESHOLD)
    );

endmodule