// SVA for motor_control
module motor_control_sva (
  input logic        clk,
  input logic        dir,
  input logic [7:0]  duty_cycle,
  input logic        h_bridge_out1,
  input logic        h_bridge_out2,
  input logic [7:0]  counter,
  input logic        pwm_out
);

  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Core functional correctness
  assert property ( !$isunknown({counter,duty_cycle,pwm_out})
                    |-> pwm_out == (counter < duty_cycle) );

  // Counter increments by 1 with wrap at 0xFF -> 0x00
  assert property ( (past_valid && !$isunknown({counter,$past(counter)}))
                    |-> ( ($past(counter) != 8'hFF) ? (counter == $past(counter)+8'd1)
                                                    : (counter == 8'h00) ) );

  // H-bridge outputs map correctly to direction and pwm_out
  assert property ( !$isunknown({dir,pwm_out,h_bridge_out1,h_bridge_out2})
                    |-> (h_bridge_out1 == (dir && pwm_out)) &&
                        (h_bridge_out2 == (!dir && pwm_out)) );

  // Never drive both outputs high simultaneously
  assert property ( !$isunknown({h_bridge_out1,h_bridge_out2})
                    |-> !(h_bridge_out1 && h_bridge_out2) );

  // When PWM is low, both outputs must be low (independent of dir)
  assert property ( !$isunknown({pwm_out,h_bridge_out1,h_bridge_out2})
                    |-> (pwm_out == 1'b0) -> (!h_bridge_out1 && !h_bridge_out2) );

  // Coverage
  // Counter wrap
  cover property ( past_valid && $past(counter) == 8'hFF && counter == 8'h00 );

  // PWM edges
  cover property ( pwm_out ##1 !pwm_out );
  cover property ( !pwm_out ##1 pwm_out );

  // Each direction actively drives its leg when PWM is high
  cover property ( dir  && pwm_out && h_bridge_out1 );
  cover property ( !dir && pwm_out && h_bridge_out2 );

  // Duty-cycle extremes
  cover property ( duty_cycle == 8'h00 && pwm_out == 1'b0 );
  cover property ( duty_cycle == 8'hFF && counter == 8'h00 && pwm_out == 1'b1 );
  cover property ( duty_cycle == 8'hFF && counter == 8'hFF && pwm_out == 1'b0 );

  // Mid duty observation
  cover property ( duty_cycle == 8'h80 && pwm_out );
  cover property ( duty_cycle == 8'h80 && !pwm_out );

  // Direction toggling while PWM is active
  cover property ( pwm_out && dir  ##1 pwm_out && !dir && h_bridge_out2 );
  cover property ( pwm_out && !dir ##1 pwm_out && dir  && h_bridge_out1 );

endmodule

// Bind into DUT (connects to internal regs)
bind motor_control motor_control_sva u_motor_control_sva (
  .clk(clk),
  .dir(dir),
  .duty_cycle(duty_cycle),
  .h_bridge_out1(h_bridge_out1),
  .h_bridge_out2(h_bridge_out2),
  .counter(counter),
  .pwm_out(pwm_out)
);