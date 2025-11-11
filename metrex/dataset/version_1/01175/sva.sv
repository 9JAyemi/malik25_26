// SVA for counter
module counter_sva(input logic clk, reset, input logic [3:0] out);
  default clocking cb @(posedge clk); endclocking

  // Interface must not be X/Z
  a_no_x_reset: assert property (!$isunknown(reset));
  a_no_x_out:   assert property (!$isunknown(out));

  // Reset (active-low) behavior
  a_reset_zero:       assert property (!reset |-> out == 4'h0);
  a_reset_fall_zero:  assert property ($fell(reset) |-> out == 4'h0);
  a_reset_rise_one:   assert property ($rose(reset) |-> out == 4'h1);

  // Running behavior: +1 modulo 16 on every cycle with reset high
  a_inc_mod16: assert property (reset && !$isunknown($past(out)) |-> out == $past(out) + 4'd1);

  // Coverage
  c_hold_reset:  cover property (!reset[*2]);
  c_deassert:    cover property ($rose(reset) && out == 4'h1);
  c_wrap:        cover property (reset && out == 4'hF |=> out == 4'h0);
endmodule

bind counter counter_sva u_counter_sva (.clk(clk), .reset(reset), .out(out));