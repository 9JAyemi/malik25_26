// SVA for counter: concise, high-quality checks and coverage
module counter_sva (
  input logic       clk,
  input logic       reset,
  input logic       enable,
  input logic [3:0] count
);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior and priority
  ap_reset_zero:        assert property (reset |-> count == 4'h0);
  ap_reset_priority:    assert property (reset && enable |-> count == 4'h0);

  // No X/Z on key signals at clock edges
  ap_no_x:              assert property (!$isunknown({reset, enable, count})));

  // Hold when disabled (synchronous reset excluded)
  ap_hold_when_disabled: assert property (disable iff (reset) !enable |=> $stable(count));

  // Increment by 1 when enabled (mod-16)
  ap_inc_when_enabled:   assert property (disable iff (reset) enable |=> count == $past(count) + 4'd1);

  // Wrap-around from 0xF to 0x0 when enabled
  ap_wrap:               assert property (disable iff (reset)
                                          $past(enable) && $past(count) == 4'hF |-> count == 4'h0);

  // Any change must be caused by prior enable (no spurious updates)
  ap_change_implies_enable: assert property (disable iff (reset)
                                             count != $past(count) |-> $past(enable));

  // First cycle after reset deassert: start from 0 and optionally increment
  ap_post_reset_step:    assert property ($past(reset) && !reset |-> count == ($past(enable) ? 4'h1 : 4'h0));

  // Functional coverage
  cp_reset_seen:         cover property (reset);
  cp_inc_seen:           cover property (disable iff (reset) enable ##1 count == $past(count)+1);
  cp_hold_seen:          cover property (disable iff (reset) !enable ##1 $stable(count));
  cp_wrap_seen:          cover property (disable iff (reset)
                                         $past(enable) && $past(count)==4'hF ##1 count==4'h0);
  cp_reset_priority:     cover property (reset && enable);
endmodule

// Bind into DUT
bind counter counter_sva u_counter_sva (.clk(clk), .reset(reset), .enable(enable), .count(count));