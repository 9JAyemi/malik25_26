// SVA checker for top_module
module top_module_sva (
  input clk,
  input reset,
  input a,
  input [3:0] counter_out,
  input [3:0] final_out,
  input rise,
  input down,
  input [3:0] counter
);
  default clocking cb @(posedge clk); endclocking

  // Sanity/no-X when out of reset
  ap_no_x: assert property (reset |-> !$isunknown({counter,counter_out,final_out,rise,down,a}));

  // Reset (active-low): hold value and release behavior
  ap_rst_hold:     assert property (!reset |-> counter == 4'd8);
  ap_rst_release:  assert property ($rose(reset) |-> counter == 4'd9 && $past(counter) == 4'd8);

  // Counter increments by 1 each cycle out of reset (mod-16)
  ap_cnt_inc: assert property (reset && $past(reset) |-> counter == $past(counter)+4'd1);

  // Simple mirrors/combinational relations
  ap_out_mirror: assert property (1'b1 |-> ##0 (counter_out == counter));
  ap_final_eq:   assert property (1'b1 |-> ##0 (final_out == counter + rise - down));

  // Edge-detect intent vs input a
  ap_rise_intent: assert property (reset && $past(reset) |-> rise == ( a && !$past(a)));
  ap_down_intent: assert property (reset && $past(reset) |-> down == (!a &&  $past(a)));
  ap_mut_excl:    assert property (reset |-> !(rise && down));
  ap_rise_pulse:  assert property (rise |=> !rise);
  ap_down_pulse:  assert property (down |=> !down);

  // Useful coverage
  cv_reset_pulse: cover property (!reset ##1 reset);
  cv_rise_seen:   cover property (reset && $rose(a));
  cv_down_seen:   cover property (reset && $fell(a));
  cv_rise_out:    cover property (reset && rise);
  cv_down_out:    cover property (reset && down);
  cv_wrap:        cover property (reset && $past(reset) && $past(counter)==4'hF && counter==4'h0);
endmodule

bind top_module top_module_sva sva_i (.*);