// SVA for counter
module counter_sva #(parameter WIDTH=4) (
  input clk,
  input reset,
  input [WIDTH-1:0] count
);
  default clocking cb @(posedge clk); endclocking

  // No X/Z on key signals
  a_no_x: assert property (!$isunknown({reset, count}));

  // Synchronous reset drives zero each cycle it's asserted (and while held)
  a_sync_reset_zero: assert property (reset |-> (count == '0));
  a_reset_hold_zero: assert property (reset && $past(reset,1,1'b0) |-> (count == '0));

  // Increment by 1 when not in reset (with wrap)
  a_inc_or_wrap: assert property ($past(!reset,1,1'b0) && !reset |-> 
                                  ((count == $past(count,1,'0) + 1) ||
                                   ($past(count,1,'0) == {WIDTH{1'b1}} && count == '0)));

  // First cycle after reset deasserts -> count is 1
  a_post_reset_one: assert property ($past(reset,1,1'b0) && !reset |-> 
                                     (count == {{(WIDTH-1){1'b0}},1'b1}));

  // Coverage: observe wraparound
  c_wrap: cover property ($past(!reset,1,1'b0) && $past(count,1,'0) == {WIDTH{1'b1}} && count == '0);
endmodule


// SVA for counter_top
module counter_top_sva (
  input clk,
  input reset,
  input [4:0] count,
  input [3:0] count1,
  input [3:0] count2
);
  default clocking cb @(posedge clk); endclocking

  a_no_x: assert property (!$isunknown({reset, count1, count2, count}));

  // Top-level count equals previous-cycle sum of sub-counters (due to NBA ordering)
  a_sum_prev: assert property (count == $past(count1,1,4'h0) + $past(count2,1,4'h0));

  // Legal range: sum of two 4-bit counters never exceeds 30
  a_range: assert property (count <= 5'd30);

  // Coverage: both counters wrap (sum=30), and both at zero (sum=0)
  c_both_wrap_to_30: cover property ($past(count1,1,4'h0)==4'hF && $past(count2,1,4'h0)==4'hF && count==5'd30);
  c_both_zero_to_zero: cover property ($past(count1,1,4'h0)==4'h0 && $past(count2,1,4'h0)==4'h0 && count==5'd0);
endmodule


// Bind SVA into DUTs
bind counter     counter_sva    #(.WIDTH(4)) counter_sva_b     (.clk(clk), .reset(reset), .count(count));
bind counter_top counter_top_sva               counter_top_sva_b(.clk(clk), .reset(reset), .count(count), .count1(count1), .count2(count2));