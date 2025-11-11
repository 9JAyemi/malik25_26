Note: ctrl is 1-bit in the DUT but used as 8-bit; the checker flags this width issue and still verifies current behavior.

module pwm_sva (
  input  logic        clk,
  input  logic        ctrl,        // as in DUT (1-bit)
  input  logic        pwm,
  input  logic [7:0]  counter,
  input  logic [7:0]  duty_cycle
);

  // Static width check for intended design (expects 8-bit ctrl)
  initial begin
    if ($bits(ctrl) != 8) $error("pwm.ctrl should be 8 bits wide for saturation to work (found %0d)", $bits(ctrl));
  end

  // Clocking and past-valid guard
  logic past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // No X/Z on key flops and input
  ap_no_x_flops:  assert property (!$isunknown({counter, duty_cycle, pwm}));
  ap_no_x_ctrl:   assert property (!$isunknown(ctrl));

  // Counter exact next-state: +1 or wrap to 0x00
  ap_cnt_next: assert property (
    counter == (($past(counter) == 8'hFF) ? 8'h00 : ($past(counter) + 8'h01))
  );

  // PWM exactly reflects previous cycle's comparison
  ap_pwm_eq: assert property (
    pwm == ($past(counter) < $past(duty_cycle))
  );

  // Duty-cycle update: saturate at 0xFF (per RTL intent) or pass-through (per current 1-bit ctrl)
  ap_duty_update: assert property (
    duty_cycle == (($past(ctrl) > 8'hFF) ? 8'hFF : $past(ctrl))
  );

  // Corner behaviors implied by the compare
  ap_duty0_forces_low:  assert property (($past(duty_cycle) == 8'h00) |-> !pwm);
  ap_dutyFF_pattern:    assert property (($past(duty_cycle) == 8'hFF) |-> pwm == ($past(counter) != 8'hFF));

  // Coverage
  cp_cnt_wrap:    cover property ($past(counter) == 8'hFF && counter == 8'h00);
  cp_pwm_rise:    cover property ($rose(pwm));
  cp_pwm_fall:    cover property ($fell(pwm));
  cp_duty_min:    cover property (duty_cycle == 8'h00);
  cp_duty_max:    cover property (duty_cycle == 8'hFF);
  cp_sat_event:   cover property ($past(ctrl) > 8'hFF && duty_cycle == 8'hFF); // unreachable with 1-bit ctrl
endmodule

// Bind example:
// bind pwm pwm_sva u_pwm_sva (.*);  // or explicitly: .clk(clk), .ctrl(ctrl), .pwm(pwm), .counter(counter), .duty_cycle(duty_cycle)