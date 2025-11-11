// SVA for Latch_Index_Pulse
// Bind into the DUT to check functional correctness and provide concise coverage.

module Latch_Index_Pulse_sva;

  // This bind module is elaborated inside Latch_Index_Pulse scope; it can see DUT signals directly.

  default clocking cb @(posedge CLK_IN); endclocking

  // Basic structural checks
  a_const1:            assert property (Constant1_out1 == 1'b1);
  a_out_eq_switch:     assert property (Out1 == Switch_out1);

  // Combinational function of the switch
  a_switch_sel_lo:     assert property ((Delay_out1 == 1'b0) |-> (Switch_out1 == In1));
  a_switch_sel_hi:     assert property ((Delay_out1 == 1'b1) |-> (Switch_out1 == 1'b1));

  // Synchronous reset behavior
  a_sync_reset_clear:  assert property (reset |-> (Delay_out1 == 1'b0));

  // Register update when enabled (allow reset to preempt on next cycle)
  a_cap_when_enb:      assert property ((!reset && enb) |-> ##1 (reset || (Delay_out1 == $past(Out1))));

  // Register holds when disabled (unless reset next cycle)
  a_hold_when_dis:     assert property ((!reset && !enb) |-> ##1 (reset || (Delay_out1 == $past(Delay_out1))));

  // Sticky-high invariant (cannot deassert without reset)
  a_sticky_high:       assert property ((!reset && Delay_out1) |-> ##1 (reset || Delay_out1));

  // Derived invariants on Out1
  a_out_high_if_lat:   assert property (Delay_out1 |-> (Out1 == 1'b1));
  a_out_follows_unlat: assert property ((Delay_out1 == 1'b0) |-> (Out1 == In1));
  a_out_zero_imp:      assert property ((Out1 == 1'b0) |-> (Delay_out1 == 1'b0 && In1 == 1'b0));

  // No X/Z on key signals when not in reset
  a_no_x:              assert property (!reset |-> !$isunknown({Out1, Switch_out1, Delay_out1, enb, In1}));

  // Coverage: latch event on a qualifying pulse
  c_latch_on_pulse:    cover property (!reset ##1 (Delay_out1 == 1'b0) ##1 (enb && In1 && !reset) ##1 (Delay_out1 && Out1));

  // Coverage: hold behavior when disabled
  c_hold_path:         cover property (!reset && (Delay_out1 == 1'b0) ##1 (!enb && !reset) ##1 (!enb && !reset && $stable(Delay_out1)));

  // Coverage: sticky-high persists until reset
  c_sticky_until_rst:  cover property (!reset && $rose(Delay_out1) ##1 Delay_out1[*3] ##1 reset);

endmodule

bind Latch_Index_Pulse Latch_Index_Pulse_sva sva_inst();