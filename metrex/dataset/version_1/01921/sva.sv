// SVA for motor_control
module motor_control_sva (
  input        clk,
  input        rst,
  input        dir,
  input  [7:0] speed,
  input        pwm_out,
  input  [1:0] motor_a_b,
  input  [7:0] counter
);

  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset clears regs immediately
  assert property (@(posedge rst) counter==8'd0 && pwm_out==1'b0 && motor_a_b==2'b00);

  // Hold reset values while rst is high
  assert property (@(posedge clk) rst |-> (counter==8'd0 && pwm_out==1'b0 && motor_a_b==2'b00
                                           && $stable(counter) && $stable(pwm_out) && $stable(motor_a_b)));

  // Direction mapping to motor drive
  assert property (@(posedge clk) disable iff (rst)  dir  |-> motor_a_b==2'b10);
  assert property (@(posedge clk) disable iff (rst) !dir  |-> motor_a_b==2'b01);

  // Counter increments when below threshold; pwm_out holds
  assert property (@(posedge clk) disable iff (rst)
                    $past(counter < $past(speed)) |-> (counter == $past(counter)+1 && pwm_out == $past(pwm_out)));

  // Threshold causes counter reset and pwm_out toggle
  assert property (@(posedge clk) disable iff (rst)
                    $past(counter >= $past(speed)) |-> (counter==8'd0 && (pwm_out != $past(pwm_out))));

  // No pwm toggle without threshold
  assert property (@(posedge clk) disable iff (rst)
                    (pwm_out != $past(pwm_out)) |-> $past(counter >= $past(speed)));

  // Counter never exceeds previous speed (handles dynamic speed safely)
  assert property (@(posedge clk) disable iff (rst) counter <= $past(speed));

  // ------------- Coverage -------------
  // Reset activity
  cover property (@(posedge clk) $rose(rst));
  cover property (@(posedge clk) $fell(rst));

  // Both directions observed
  cover property (@(posedge clk) disable iff (rst) dir  && motor_a_b==2'b10);
  cover property (@(posedge clk) disable iff (rst) !dir && motor_a_b==2'b01);

  // Observe pwm toggle events
  cover property (@(posedge clk) disable iff (rst) (pwm_out != $past(pwm_out)));

  // Corner speeds
  cover property (@(posedge clk) disable iff (rst) speed==8'd0 ##1 (pwm_out != $past(pwm_out)) ##1 (pwm_out != $past(pwm_out)));
  cover property (@(posedge clk) disable iff (rst) speed==8'hFF && counter==8'hFF);

endmodule

bind motor_control motor_control_sva mtr_ctl_sva (.*);