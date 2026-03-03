// SVA checker for pwm_generator
module pwm_generator_sva (
  input logic clk,
  input logic rst_n,
  input logic pwm_out
);

  default clocking cb @(posedge clk); endclocking

  // Async reset forces immediate low
  ap_async_reset_low: assert property (@(negedge rst_n) ##0 (pwm_out == 1'b0));

  // While in reset, output stays low on every clock
  ap_hold_low_in_reset: assert property (!rst_n |=> pwm_out == 1'b0);

  // First active cycle after reset release drives 1
  ap_first_cycle_high: assert property ($rose(rst_n) |=> pwm_out == 1'b1);

  // Out of reset (stable), pwm_out toggles every clock
  ap_toggle_each_clk: assert property ((rst_n && $past(rst_n)) |-> (pwm_out != $past(pwm_out)));

  // Out of reset (stable), no X/Z on output
  ap_no_x_out: assert property ((rst_n && $past(rst_n)) |-> !$isunknown(pwm_out));

  // Output changes only due to clk posedge (NBA of it) or async reset assertion
  ap_change_only_on_clk_or_rst: assert property (@(posedge pwm_out or negedge pwm_out) (clk || !rst_n));

  // Coverage
  cp_async_reset_seen:      cover property (@(negedge rst_n) ##0 (pwm_out == 1'b0));
  cp_release_then_toggles:  cover property (@(posedge clk) $rose(rst_n) ##1 (pwm_out == 1'b1) ##1 (pwm_out == 1'b0));
  cp_sustained_toggle:      cover property (@(posedge clk) disable iff (!rst_n) (pwm_out != $past(pwm_out)) [*6]);

endmodule

// Bind into DUT
bind pwm_generator pwm_generator_sva u_pwm_generator_sva (.clk(clk), .rst_n(rst_n), .pwm_out(pwm_out));