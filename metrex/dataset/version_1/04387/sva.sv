// SVA for switch_to_leds
// Bind these assertions to the DUT for combinational functional checking and coverage.

module switch_to_leds_sva (
  input logic [15:0] switch_input,
  input logic        reset,
  input logic [7:0]  red_led_output,
  input logic [7:0]  green_led_output
);

  // Use value-change event to check combinational relationships; ##0 avoids race with NBA updates.
  default clocking cb @(switch_input or reset or red_led_output or green_led_output); endclocking

  // Reset drives both outputs to 0
  property p_reset_outputs_zero;
    reset |-> ##0 (red_led_output == 8'h00 && green_led_output == 8'h00);
  endproperty
  assert property (p_reset_outputs_zero);

  // Functional mapping when not in reset (case equality allows X-propagation consistency)
  property p_invert_map_no_reset;
    !reset |-> ##0 ((red_led_output  === ~switch_input[7:0]) &&
                    (green_led_output === ~switch_input[15:8]));
  endproperty
  assert property (p_invert_map_no_reset);

  // When inputs are known and not in reset, outputs must be known
  property p_no_x_outputs_when_inputs_known;
    (!reset && !$isunknown(switch_input)) |-> ##0
      (!$isunknown(red_led_output) && !$isunknown(green_led_output));
  endproperty
  assert property (p_no_x_outputs_when_inputs_known);

  // No output changes unless inputs change (combinational stability)
  property p_no_glitch_without_input_change;
    (!reset && $stable(switch_input)) |-> ##0 $stable({red_led_output, green_led_output});
  endproperty
  assert property (p_no_glitch_without_input_change);

  // Coverage: reset seen, deassertion seen, and a few key data patterns
  cover property (reset);
  cover property ($fell(reset));
  cover property (!reset && switch_input == 16'h0000 ##0 (red_led_output == 8'hFF && green_led_output == 8'hFF));
  cover property (!reset && switch_input == 16'hFFFF ##0 (red_led_output == 8'h00 && green_led_output == 8'h00));
  cover property (!reset && switch_input == 16'hA5C3 ##0 (red_led_output == ~8'hC3 && green_led_output == ~8'hA5));

endmodule

// Bind to DUT
bind switch_to_leds switch_to_leds_sva sva_i (
  .switch_input     (switch_input),
  .reset            (reset),
  .red_led_output   (red_led_output),
  .green_led_output (green_led_output)
);