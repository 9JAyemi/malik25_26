// SVA for pwm_generator
// Bind these assertions to the DUT. They check reset behavior, counter up/saturate,
// PWM output behavior, X-prop, and provide compact coverage.

module pwm_generator_sva #(parameter int WIDTH = 7)(
  input logic              clk,
  input logic              rst,
  input logic              input_signal,
  input logic              pwm_signal,
  input logic [WIDTH-1:0]  duty_cycle
);
  localparam int unsigned MAX = (1<<WIDTH)-1;

  default clocking cb @(posedge clk); endclocking
  default disable iff ($initstate);

  // Reset values
  a_reset_vals:      assert property (rst |-> (pwm_signal==1'b0 && duty_cycle=='0));

  // PWM output is always 1 when not in reset
  a_pwm_high_nr:     assert property (!rst |-> pwm_signal==1'b1);

  // Counter increments by 1 each cycle until MAX (guarded to avoid crossing reset)
  a_cnt_inc:         assert property (!rst && $past(!rst) && ($past(duty_cycle) <  MAX)
                                      |-> duty_cycle == $past(duty_cycle)+1);

  // Counter saturates at MAX
  a_cnt_sat:         assert property (!rst && $past(!rst) && ($past(duty_cycle) == MAX)
                                      |-> duty_cycle == MAX);

  // Monotonic non-decreasing (redundant safety net)
  a_cnt_monotonic:   assert property (!rst && $past(!rst) |-> duty_cycle >= $past(duty_cycle));

  // First cycle after reset deassertion: pwm=1, duty=1 (since reset drove duty=0)
  a_post_reset_step: assert property ($fell(rst) |-> (pwm_signal==1'b1 && duty_cycle=={{(WIDTH-1){1'b0}},1'b1}));

  // Range/X checks
  a_cnt_range:       assert property (!rst |-> duty_cycle <= MAX);
  a_no_x:            assert property (!$isunknown({rst,pwm_signal}) && (!rst |-> !$isunknown(duty_cycle)));

  // Compact coverage
  c_rst_assert:      cover  property ($rose(rst));
  c_rst_deassert:    cover  property ($fell(rst));
  c_reach_max:       cover  property (!rst ##[1:$] (duty_cycle==MAX));
  c_hold_at_max:     cover  property (!rst && duty_cycle==MAX ##1 duty_cycle==MAX ##1 duty_cycle==MAX);
  c_input_toggles:   cover  property (!rst && $changed(input_signal));
endmodule

// Bind into all instances of pwm_generator (connect internal duty_cycle hierarchically)
bind pwm_generator pwm_generator_sva #(.WIDTH(7))
  pwm_generator_sva_i ( .clk(clk), .rst(rst), .input_signal(input_signal), .pwm_signal(pwm_signal), .duty_cycle(duty_cycle) );