// SVA checker bound into the DUT. Focused, high-quality checks and coverage.
module gray_to_binary_sva();
  // This checker is intended to be bound into gray_to_binary and
  // uses hierarchical access to DUT signals.
  default clocking cb @(posedge clk); endclocking

  // 1) Reset behavior (synchronous, dominates enable)
  a_reset_sync: assert property (rst |-> (gray_reg1==4'h0 && gray_reg2==4'h0 &&
                                          binary_reg1==4'h0 && binary_reg2==4'h0 &&
                                          binary==4'h0));
  a_rst_dominates_enable: assert property (rst && ena |-> (gray_reg1==4'h0 && gray_reg2==4'h0 &&
                                                           binary_reg1==4'h0 && binary_reg2==4'h0));

  // 2) Output wiring
  a_out_wired: assert property (binary == binary_reg2);

  // 3) Hold behavior when disabled
  a_hold_when_disabled: assert property (!rst && !ena |-> $stable({gray_reg1,gray_reg2,binary_reg1,binary_reg2,binary}));

  // 4) Pipeline update equations when enabled (non-blocking RHS are $past values)
  a_update_when_enabled: assert property (!rst && ena |-> (
      gray_reg1  == $past(gray)        &&
      gray_reg2  == $past(gray_reg1)   &&
      binary_reg1== $past(binary_reg2) &&
      binary_reg2== ($past(binary_reg1) ^ $past(gray_reg2))
  ));

  // 5) Two-cycle gray pipeline latency under consecutive enables
  a_two_cycle_gray_latency: assert property (!rst && $past(ena) && ena |-> gray_reg2 == $past(gray,2));

  // 6) No X/Z propagation in normal operation
  a_no_unknowns: assert property (!rst |-> !$isunknown({ena,gray,gray_reg1,gray_reg2,binary_reg1,binary_reg2,binary}));

  // Coverage: reset, single and burst enables, observable output change
  c_reset_seen:          cover property (rst);
  c_enable_single_pulse: cover property (!rst && !ena ##1 ena ##1 !ena);
  c_enable_burst2:       cover property (!rst && ena ##1 ena);
  c_enable_burst3:       cover property (!rst && ena [*3]);
  c_binary_changes:      cover property (!rst && ena && (binary != $past(binary)));
endmodule

bind gray_to_binary gray_to_binary_sva sva_inst();