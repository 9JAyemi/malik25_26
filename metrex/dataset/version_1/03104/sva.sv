// SVA for motor_controller
// Bindable checker with concise, high-value properties

module motor_controller_sva #(
  parameter int max_pwm_width = 255
)(
  input  logic        clk,
  input  logic [7:0]  pwm_width,
  input  logic        dir,
  input  logic        pwm,
  input  logic        hbridge_out1,
  input  logic        hbridge_out2,
  // internal state tap
  input  logic [7:0]  pwm_counter
);

  default clocking cb @ (posedge clk); endclocking

  // Basic sanity / X checks
  assert property (cb !$isunknown({pwm_width, dir, pwm, hbridge_out1, hbridge_out2, pwm_counter}));
  assert property (cb pwm_width <= max_pwm_width);
  assert property (cb pwm_counter <= max_pwm_width);

  // Counter next-state function
  assert property (cb ($past(pwm_counter) != max_pwm_width) |-> (pwm_counter == $past(pwm_counter)+1));
  assert property (cb ($past(pwm_counter) == max_pwm_width) |-> (pwm_counter == 0 && pwm == 0));

  // PWM function: registered result of (pwm_counter < pwm_width)
  assert property (cb pwm == ($past(pwm_counter) < $past(pwm_width)));

  // H-bridge: complementary outputs and inversion of dir (1-cycle due to sampling semantics)
  assert property (cb hbridge_out1 == ~hbridge_out2);
  assert property (cb hbridge_out1 == ~$past(dir) && hbridge_out2 == $past(dir));

  // Coverage
  cover property (cb pwm_counter == max_pwm_width ##1 pwm_counter == 0);          // wrap
  cover property (cb $rose(dir));                                                  // dir change
  cover property (cb $fell(dir));                                                  // dir change
  cover property (cb pwm_width == 0);                                              // 0% duty
  cover property (cb pwm_width == max_pwm_width);                                  // near-100% duty
  cover property (cb (pwm_counter==0 && pwm_width>0 && pwm_width<max_pwm_width)
                      |-> ##[1:max_pwm_width] (!pwm));                             // hi then low within a period

endmodule

// Example bind (place in a separate file or a testbench)
// bind motor_controller motor_controller_sva #(.max_pwm_width(max_pwm_width))
//   mc_sva (.* , .pwm_counter(pwm_counter));