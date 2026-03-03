// SVA for binary_counter
module binary_counter_sva (
  input clk,
  input reset,
  input enable,
  input [3:0] count
);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  a_reset_clears_next:    assert property (reset |=> count == 4'd0);
  a_reset_holds_zero:     assert property (reset && $past(reset) |-> count == 4'd0);

  // Functional behavior
  a_hold_when_disabled:   assert property (disable iff (reset) (!enable) |=> count == $past(count));
  a_inc_when_enabled:     assert property (disable iff (reset) (enable)   |=> count == (($past(count)+4'd1) & 4'hF));
  a_change_requires_en:   assert property ((!reset && !$past(reset) && $changed(count)) |-> $past(enable));

  // Sanity
  a_count_known:          assert property (disable iff (reset) !$isunknown(count));

  // Coverage
  c_reset_clear:          cover  property (reset ##1 count == 4'd0);
  c_inc_after_reset:      cover  property (reset ##1 !reset ##1 enable ##1 count == 4'd1);
  c_wraparound:           cover  property (disable iff (reset) ($past(count)==4'hF && enable) ##1 (count==4'h0));
  c_hold_case:            cover  property (disable iff (reset) (!enable && $past(!enable) && count==$past(count)));
endmodule

// Bind into DUT
bind binary_counter binary_counter_sva sva_i (.*);