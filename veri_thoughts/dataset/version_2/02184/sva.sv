module light_control_block_sva (
  input logic [7:0] analog_in,
  input logic       enable,
  input logic       clk,
  input logic [7:0] pwm_out
);
  // Clock: clk. No reset in RTL.
  // Mixed logic: combinational duty_cycle=analog_in/255; sequential pwm_out register.
  // Behavior (resolution=8): when enable=1, next pwm_out is 1 iff analog_in==8'hFF, else 0; when enable=0, next pwm_out=0.

  // Next-cycle pwm_out matches exact mapping from current inputs.
  check_next_output_exact_mapping: assert property (
    @(posedge clk) 1'b1 |=> (pwm_out == {7'b0, (enable && (analog_in == 8'hFF))})
  );

  // When disabled, next pwm_out is 0.
  check_disable_forces_zero_next: assert property (
    @(posedge clk) (!enable) |=> (pwm_out == 8'h00)
  );

  // With enable and max input, next pwm_out is 1.
  check_enable_and_max_sets_one_next: assert property (
    @(posedge clk) (enable && (analog_in == 8'hFF)) |=> (pwm_out == 8'h01)
  );

  // With enable and non-max input, next pwm_out is 0.
  check_enable_and_not_max_sets_zero_next: assert property (
    @(posedge clk) (enable && (analog_in != 8'hFF)) |=> (pwm_out == 8'h00)
  );

  // Next-cycle upper bits of pwm_out are always zero.
  check_next_upper_bits_zero: assert property (
    @(posedge clk) 1'b1 |=> (pwm_out[7:1] == 7'b0)
  );

  // If pwm_out is 1 now, previous cycle had enable=1 and analog_in==8'hFF.
  check_one_implies_prev_enable_and_max: assert property (
    @(posedge clk) (pwm_out == 8'h01) |-> $past(enable && (analog_in == 8'hFF))
  );

  // If inputs are stable across a cycle, next pwm_out equals previous pwm_out.
  check_stable_inputs_keep_output_next: assert property (
    @(posedge clk) ($stable(enable) && $stable(analog_in)) |-> ##1 (pwm_out == $past(pwm_out))
  );

  // A falling edge on enable forces next pwm_out to 0.
  check_enable_fall_clears_next: assert property (
    @(posedge clk) $fell(enable) |=> (pwm_out == 8'h00)
  );

  // Rising to max analog_in with enable set makes next pwm_out 1.
  check_analog_rise_to_max_sets_one_next: assert property (
    @(posedge clk) (enable && (analog_in == 8'hFF) && $past(analog_in != 8'hFF)) |=> (pwm_out == 8'h01)
  );

  // Falling from max analog_in with enable set makes next pwm_out 0.
  check_analog_fall_from_max_clears_next: assert property (
    @(posedge clk) (enable && (analog_in != 8'hFF) && $past(analog_in == 8'hFF)) |=> (pwm_out == 8'h00)
  );

endmodule