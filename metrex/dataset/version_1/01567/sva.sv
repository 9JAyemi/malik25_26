// SVA checker for pwm
module pwm_sva #(
  parameter int unsigned PWM_DEFAULT = 8'd150
)(
  input  logic        clk,
  input  logic        rst,
  input  logic [7:0]  pwm_duty,
  input  logic [7:0]  pwm_offset,
  input  logic        pwm_out,
  input  logic        pwm_buffer,
  input  logic [7:0]  counter,
  input  logic [7:0]  duty_check
);

  default clocking cb @(posedge clk); endclocking

  // Reset behavior (async reset held high)
  assert property (@cb rst |-> (counter==8'd0 && pwm_buffer && pwm_out));
  assert property (@cb rst && $past(rst) |-> (counter==8'd0 && pwm_buffer && pwm_out));

  // Run-time checks
  default disable iff (rst);

  // Local recompute of DUT math (8-bit wrap semantics)
  let duty_temp8 = bit [7:0]'(pwm_duty + (pwm_offset - PWM_DEFAULT));

  // duty_check correctness and range
  assert property (@cb (duty_temp8 inside {[8'd50:8'd250]}) |-> (duty_check == duty_temp8));
  assert property (@cb !(duty_temp8 inside {[8'd50:8'd250]}) |-> (duty_check == PWM_DEFAULT));
  assert property (@cb (duty_check == PWM_DEFAULT) || (duty_check inside {[8'd50:8'd250]}));

  // Output mirrors buffer
  assert property (@cb pwm_out == pwm_buffer);

  // Combinational decision: buffer reflects compare
  assert property (@cb pwm_buffer == (counter <= duty_check));

  // Next-state counter semantics
  assert property (@cb (counter <= duty_check) |=> (counter == $past(counter) + 8'd1));
  assert property (@cb (counter >  duty_check) |=> (counter == $past(counter)));

  // No X/Z on key regs/nets during operation
  assert property (@cb !$isunknown({pwm_buffer, pwm_out, counter, duty_check}));

  // Functional coverage
  cover property (@cb (counter == duty_check) ##1 $fell(pwm_buffer));   // boundary crossing
  cover property (@cb duty_check == 8'd50);
  cover property (@cb duty_check == 8'd250);
  cover property (@cb (duty_temp8 inside {[8'd50:8'd250]}));            // in-range path
  cover property (@cb !(duty_temp8 inside {[8'd50:8'd250]}));           // default path
  cover property (@cb $fell(pwm_buffer) ##[1:$] $rose(pwm_buffer));     // re-enable after threshold change

endmodule

// Bind into DUT
bind pwm pwm_sva #(.PWM_DEFAULT(PWM_DEFAULT)) pwm_sva_i (
  .clk(clk),
  .rst(rst),
  .pwm_duty(pwm_duty),
  .pwm_offset(pwm_offset),
  .pwm_out(pwm_out),
  .pwm_buffer(pwm_buffer),
  .counter(counter),
  .duty_check(duty_check)
);