// SVA for counter. Bind this to the DUT.

module counter_sva (
  input clk,
  input rst,
  input up_down,
  input [7:0] count
);

  default clocking cb @(posedge clk); endclocking

  // Track availability of $past()
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Synchronous reset drives zero
  a_rst_zero:  assert property (rst |-> count == 8'd0);

  // No X/Z on key signals out of reset
  a_known:     assert property (disable iff (rst) !$isunknown({up_down, count}));

  // Single-step behavior with correct direction, including wraps:
  // delta = +1 when up_down==1, delta = -1 (0xFF) when up_down==0
  a_step_dir:  assert property (disable iff (rst || !past_valid)
                                ((count - $past(count)) == (up_down ? 8'h01 : 8'hFF)));

  // Count must change every cycle out of reset
  a_changes:   assert property (disable iff (rst || !past_valid) count != $past(count));

  // Coverage: exercise modes, endpoints, wraps, and direction toggle
  c_up_mode:      cover property (disable iff (rst) up_down);
  c_down_mode:    cover property (disable iff (rst) !up_down);
  c_hit_zero:     cover property (count == 8'h00);
  c_hit_max:      cover property (count == 8'hFF);
  c_up_wrap:      cover property (disable iff (rst || !past_valid) up_down && $past(count) == 8'hFF);
  c_down_wrap:    cover property (disable iff (rst || !past_valid) !up_down && $past(count) == 8'h00);
  c_dir_toggle:   cover property (disable iff (rst || !past_valid) $changed(up_down));

endmodule

bind counter counter_sva counter_sva_i (.*);