// SVA checker for PWM
module PWM_sva (
  input  logic        clk,
  input  logic [7:0]  ctrl,
  input  logic [15:0] period,
  input  logic        pwm_out,
  input  logic [15:0] count,
  input  logic [7:0]  duty_cycle
);
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Functional correctness
  ap_duty_reg: assert property (@(posedge clk) disable iff (!past_valid)
    duty_cycle == $past(ctrl));

  ap_count_inc: assert property (@(posedge clk) disable iff (!past_valid)
    ($past(count) < $past(period)) |-> (count == $past(count) + 16'h1));

  ap_count_wrap: assert property (@(posedge clk) disable iff (!past_valid)
    ($past(count) >= $past(period)) |-> (count == 16'h0));

  ap_pwm_match: assert property (@(posedge clk) disable iff (!past_valid)
    pwm_out == ($past(count) < $past(duty_cycle)));

  // Useful corner checks
  ap_duty_zero_low: assert property (@(posedge clk) disable iff (!past_valid)
    ($past(duty_cycle) == 8'h0) |-> !pwm_out);

  ap_duty_gt_period_all_high: assert property (@(posedge clk) disable iff (!past_valid)
    ($past(duty_cycle) > $past(period)) |-> pwm_out);

  // Coverage
  cp_wrap:          cover property (@(posedge clk) past_valid && $past(count) >= $past(period) ##1 (count == 16'h0));
  cp_pwm_l2h:       cover property (@(posedge clk) past_valid && !pwm_out ##1 pwm_out);
  cp_pwm_h2l:       cover property (@(posedge clk) past_valid &&  pwm_out ##1 !pwm_out);
  cp_duty_zero:     cover property (@(posedge clk) past_valid && ($past(duty_cycle) == 8'h0) && !pwm_out);
  cp_duty_saturate: cover property (@(posedge clk) past_valid && ($past(duty_cycle) > $past(period)) && pwm_out);
endmodule

// Bind into DUT (accesses internal regs count and duty_cycle)
bind PWM PWM_sva u_pwm_sva (
  .clk(clk),
  .ctrl(ctrl),
  .period(period),
  .pwm_out(pwm_out),
  .count(count),
  .duty_cycle(duty_cycle)
);