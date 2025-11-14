// SVA for pwm_generator
// Bind this module to the DUT: bind pwm_generator pwm_generator_sva #(.PWM_DEPTH(PWM_DEPTH)) u_sva();

module pwm_generator_sva #(parameter int PWM_DEPTH = 8);

  // Access DUT scope signals via bind (no ports)
  // Assumes names: clk, rst_n, enable, duty_cycle, PWM_out, counter, threshold
  localparam int unsigned MAX = (1 << PWM_DEPTH) - 1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Basic sanity
  assert property (!$isunknown({counter, PWM_out, threshold}));
  assert property (!rst_n |-> (counter == '0 && PWM_out == 1'b0));

  // Input range (percentage, 0..100)
  assert property ($unsigned(duty_cycle) <= 100);

  // Threshold function matches spec
  assert property ($unsigned(threshold) == (MAX * $unsigned(duty_cycle)) / 100);

  // Hold behavior when disabled
  assert property (!enable |=> (counter == $past(counter) && PWM_out == $past(PWM_out)));

  // Next-state function when previously enabled
  assert property ($past(enable) |-> ($unsigned(counter) ==
                                      (($unsigned($past(counter)) >= $unsigned(threshold)) ? 0
                                                                                            : $unsigned($past(counter)) + 1)));
  assert property ($past(enable) |-> (PWM_out == ($unsigned($past(counter)) >= $unsigned(threshold))));

  // No X on interface when out of reset (optional but useful)
  assert property (!$isunknown({rst_n, enable, duty_cycle}));

  // Coverage
  cover property ($rose(rst_n));  // reset release
  // 0% duty -> always 1 when enabled
  cover property (enable && (threshold == 0) && PWM_out ##1 enable && PWM_out ##1 enable && PWM_out);
  // Max duty -> periodic single-cycle pulse
  cover property (enable && (threshold == MAX) && PWM_out
                  ##[1:$] (enable && (threshold == MAX) && PWM_out));
  // Mid duty -> see at least one pulse
  cover property (enable && (threshold inside {[1:MAX-1]})
                  ##[1:$] PWM_out);
  // Enable gating toggles
  cover property (enable ##1 !enable ##1 enable);
  // Wrap event observed
  cover property ($past(enable) && ($unsigned($past(counter)) >= $unsigned(threshold)) && PWM_out && (counter == '0));

endmodule

// Bind into DUT
bind pwm_generator pwm_generator_sva #(.PWM_DEPTH(PWM_DEPTH)) u_pwm_generator_sva();