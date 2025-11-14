// SVA for motor_control_block
// Bind into the DUT; references internal regs (pwm_counter, pwm_out_reg).

bind motor_control_block motor_control_block_asserts #(.pwm_freq(pwm_freq)) ();

module motor_control_block_asserts #(parameter int pwm_freq = 100) ();
  // Local constants
  localparam int HALF  = pwm_freq/2;
  localparam logic [7:0] HALF8 = HALF[7:0];

  // Optional static param sanity
  initial begin
    if (HALF <= 0 || HALF > 8'hFF) $error("motor_control_block: pwm_freq/2 (%0d) must be in 1..255 for 8-bit counter", HALF);
  end

  default clocking cb @(posedge clk); endclocking

  // Pass-throughs
  a_hbridge_passthru: assert property (hbridge_out == hbridge_ctrl);
  a_stepper_passthru: assert property (stepper_out == stepper_ctrl);
  a_pwm_net_tied:     assert property (pwm_out == pwm_out_reg);

  // Counter increments by +1 mod 256 (after values become known)
  a_cnt_inc: assert property (
    $past(1'b1) && !$isunknown($past(pwm_counter)) && !$isunknown(pwm_counter)
      |-> pwm_counter == $past(pwm_counter) + 8'd1
  );

  // PWM edges occur exactly at thresholds (next cycle observes effect)
  a_pwm_set_hi: assert property ( (pwm_counter == 8'd0)     |=> pwm_out );
  a_pwm_set_lo: assert property ( (pwm_counter == HALF8)    |=> !pwm_out );

  // PWM does not change except at thresholds
  a_pwm_change_only_on_thresholds: assert property (
    $past(1'b1) && $changed(pwm_out)
      |-> ($past(pwm_counter) == 8'd0 || $past(pwm_counter) == HALF8)
  );

  // PWM holds value when not at thresholds
  a_pwm_stable_off_thresholds: assert property (
    !((pwm_counter == 8'd0) || (pwm_counter == HALF8)) |=> $stable(pwm_out)
  );

  // No unknowns on outputs
  a_no_x_outs: assert property ( !$isunknown({pwm_out, hbridge_out, stepper_out}) );

  // Coverage
  c_pwm_hi_then_lo: cover property ( (pwm_counter==8'd0) ##1 pwm_out ##[1:$] (pwm_counter==HALF8) ##1 !pwm_out );
  c_pwm_lo_then_hi: cover property ( (pwm_counter==HALF8) ##1 !pwm_out ##[1:$] (pwm_counter==8'd0) ##1 pwm_out );
  c_pwm_edges:      cover property ( $rose(pwm_out) );  // see a rise at least once
  c_pwm_edges2:     cover property ( $fell(pwm_out) );  // see a fall at least once
  c_hbridge_toggle: cover property ( $changed(hbridge_ctrl) && (hbridge_out==hbridge_ctrl) );
  c_stepper_toggle: cover property ( $changed(stepper_ctrl) && (stepper_out==stepper_ctrl) );
endmodule