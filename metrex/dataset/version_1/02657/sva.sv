// SVA for min_max_tracker
module mmt_sva (
  input  logic        clk,
  input  logic [7:0]  adc_d,
  input  logic [7:0]  threshold,
  input  logic [7:0]  min,
  input  logic [7:0]  max,
  input  logic [7:0]  min_val,
  input  logic [7:0]  max_val,
  input  logic [7:0]  cur_min_val,
  input  logic [7:0]  cur_max_val,
  input  logic [1:0]  state
);

  default clocking cb @(posedge clk); endclocking
  default disable iff ($initstate || $isunknown({state,adc_d,threshold,cur_min_val,cur_max_val,min_val,max_val}));

  // Helpful predicates (respecting else-if priorities)
  let s0_to_2        = (cur_max_val >= ({1'b0,adc_d} + threshold));
  let s0_to_1        = (!s0_to_2) && (adc_d >= ({1'b0,cur_min_val} + threshold));

  let s1_update_max  = (cur_max_val <= adc_d);
  let s1_to_2        = (!s1_update_max) && (({1'b0,adc_d} + threshold) <= cur_max_val);

  let s2_update_min  = (adc_d <= cur_min_val);
  let s2_to_1        = (!s2_update_min) && (adc_d >= ({1'b0,cur_min_val} + threshold));

  // Basic invariants
  assert property (state inside {2'd0,2'd1,2'd2});
  assert property (min == min_val && max == max_val);

  // State 0 transitions and updates
  assert property (state==2'd0 && s0_to_2 |=> state==2'd2);
  assert property (state==2'd0 && s0_to_1 |=> state==2'd1);
  assert property (state==2'd0 && !(s0_to_2 || s0_to_1) |=> state==2'd0);

  assert property (state==2'd0 && (cur_max_val <= adc_d) |=> cur_max_val == $past(adc_d));
  assert property (state==2'd0 && !(cur_max_val <= adc_d) && (adc_d <= cur_min_val) |=> cur_min_val == $past(adc_d));
  assert property (state==2'd0 && !(cur_max_val <= adc_d) && !(adc_d <= cur_min_val) |=> $stable({cur_min_val,cur_max_val}));

  // State 1 priority, transition, and updates
  assert property (state==2'd1 && s1_update_max |=> state==2'd1 && cur_max_val == $past(adc_d));
  assert property (state==2'd1 && s1_to_2 |=> state==2'd2 && cur_min_val == $past(adc_d) && max_val == $past(cur_max_val));
  assert property (state==2'd1 && !s1_update_max && !s1_to_2 |=> state==2'd1 && $stable({cur_min_val,cur_max_val,max_val}));

  // State 2 priority, transition, and updates
  assert property (state==2'd2 && s2_update_min |=> state==2'd2 && cur_min_val == $past(adc_d));
  assert property (state==2'd2 && s2_to_1 |=> state==2'd1 && cur_max_val == $past(adc_d) && min_val == $past(cur_min_val));
  assert property (state==2'd2 && !s2_update_min && !s2_to_1 |=> state==2'd2 && $stable({cur_min_val,cur_max_val,min_val}));

  // Latch update gating: min/max only change on their respective cross-threshold events
  assert property ($changed(min_val) |-> $past(state)==2'd2 && $past(s2_to_1) && state==2'd1 && min_val == $past(cur_min_val));
  assert property ($changed(max_val) |-> $past(state)==2'd1 && $past(s1_to_2) && state==2'd2 && max_val == $past(cur_max_val));

  // Never change cur_min_val and cur_max_val in the same cycle
  assert property (!($changed(cur_min_val) && $changed(cur_max_val)));

  // Functional coverage
  cover property (state==2'd0 ##1 state==2'd1);
  cover property (state==2'd0 ##1 state==2'd2);
  cover property (state==2'd1 && s1_to_2 |=> state==2'd2 && $changed(max_val));
  cover property (state==2'd2 && s2_to_1 |=> state==2'd1 && $changed(min_val));
  cover property (state==2'd1 && s1_update_max |=> cur_max_val == $past(adc_d));
  cover property (state==2'd2 && s2_update_min |=> cur_min_val == $past(adc_d));

endmodule

// Bind into the DUT
bind min_max_tracker mmt_sva mmt_sva_i (
  .clk(clk),
  .adc_d(adc_d),
  .threshold(threshold),
  .min(min),
  .max(max),
  .min_val(min_val),
  .max_val(max_val),
  .cur_min_val(cur_min_val),
  .cur_max_val(cur_max_val),
  .state(state)
);