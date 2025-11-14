// SVA for RC_Oscillator
// Bind into the DUT to access internals (count, state, out, clk)
module RC_Osc_SVA;
  // Use DUT's clock
  default clocking cb @(posedge clk); endclocking

  // Guard $past on/after first clock
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Known-value checks after first sampled cycle
  ap_count_known: assert property (past_valid |-> !$isunknown(count));
  ap_state_known: assert property (past_valid |-> !$isunknown(state));
  ap_out_known:   assert property (past_valid |-> !$isunknown(out));

  // Count increments by 1 with wrap
  ap_count_steps: assert property (past_valid |-> 
      (($past(count) != 32'hFFFF_FFFF && count == $past(count) + 32'd1) ||
       ($past(count) == 32'hFFFF_FFFF && count == 32'h0000_0000)));

  // State toggles iff current sampled count is zero
  ap_state_toggle_when_count0:     assert property (past_valid && (count == 32'h0) |-> state != $past(state));
  ap_state_stable_when_count_not0: assert property (past_valid && (count != 32'h0) |-> state == $past(state));

  // Output changes iff state changes (no extra/spurious edges)
  ap_out_changes_with_state: assert property (past_valid |-> (out ^ $past(out)) == (state ^ $past(state)));

  // Output equals state after delta (handle NBA scheduling in comb block)
  ap_out_eq_state_delta: assert property (##0 (out === state));

  // Count leaves zero on the next cycle
  ap_count_leaves_zero: assert property (count == 32'h0 |=> count == 32'h1);

  // Coverage
  cp_state_toggle: cover property (past_valid && (state != $past(state)));
  cp_out_rise:     cover property (past_valid && $rose(out));
  cp_out_fall:     cover property (past_valid && $fell(out));
  cp_wrap:         cover property (past_valid && ($past(count) == 32'hFFFF_FFFF) && (count == 32'h0));
endmodule

bind RC_Oscillator RC_Osc_SVA rc_osc_sva_i();