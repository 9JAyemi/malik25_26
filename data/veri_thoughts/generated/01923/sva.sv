module switch_to_leds_sva (
    input  logic [15:0] switch_input,
    input  logic        reset,
    input  logic [7:0]  red_led_output,
    input  logic [7:0]  green_led_output
);
    // Using $global_clock for combinational sampling; reset is active-high.

    // During reset, both LED outputs are driven to zero.
    reset_forces_zeros: assert property (
        @($global_clock) reset |-> (red_led_output == 8'b0) && (green_led_output == 8'b0)
    );

    // When not in reset, red LED equals bitwise NOT of switch_input[7:0].
    red_mapping_when_not_reset: assert property (
        @($global_clock) disable iff (reset) red_led_output == ~switch_input[7:0]
    );

    // When not in reset, green LED equals bitwise NOT of switch_input[15:8].
    green_mapping_when_not_reset: assert property (
        @($global_clock) disable iff (reset) green_led_output == ~switch_input[15:8]
    );

    // When not in reset, concatenated {green,red} equals bitwise NOT of full switch_input.
    concat_mapping_when_not_reset: assert property (
        @($global_clock) disable iff (reset) {green_led_output, red_led_output} == ~switch_input
    );

    // With reset deasserted, if switch_input is stable, both LED outputs remain stable.
    stable_inputs_imply_stable_outputs: assert property (
        @($global_clock) disable iff (reset) $stable(switch_input) |-> $stable({green_led_output, red_led_output})
    );

    // With reset deasserted, change only in low byte changes only red LEDs; green LEDs stay stable.
    low_half_change_affects_only_red: assert property (
        @($global_clock) disable iff (reset) ($changed(switch_input[7:0]) && $stable(switch_input[15:8])) |-> ($changed(red_led_output) && $stable(green_led_output))
    );

    // With reset deasserted, change only in high byte changes only green LEDs; red LEDs stay stable.
    high_half_change_affects_only_green: assert property (
        @($global_clock) disable iff (reset) ($changed(switch_input[15:8]) && $stable(switch_input[7:0])) |-> ($changed(green_led_output) && $stable(red_led_output))
    );

    // With reset deasserted, any change to switch_input changes the concatenated LED outputs.
    any_input_change_changes_outputs: assert property (
        @($global_clock) disable iff (reset) $changed(switch_input) |-> $changed({green_led_output, red_led_output})
    );

    // With reset deasserted, a change in red LEDs implies the low byte of switch_input changed.
    red_change_implies_low_input_change: assert property (
        @($global_clock) disable iff (reset) ($changed(red_led_output) && $stable(switch_input[15:8])) |-> $changed(switch_input[7:0])
    );

    // With reset deasserted, a change in green LEDs implies the high byte of switch_input changed.
    green_change_implies_high_input_change: assert property (
        @($global_clock) disable iff (reset) ($changed(green_led_output) && $stable(switch_input[7:0])) |-> $changed(switch_input[15:8])
    );

endmodule