// SVA for synchronizer
// Bind into the DUT to access internals without modifying RTL.

module synchronizer_sva;
  // Bound inside 'synchronizer' scope; can see internal regs
  default clocking cb @(posedge clk_in); endclocking

  // Pipeline consistency: 2-flop chain and output mapping
  a_pipeline_consistency: assert property (
      (async_sync_prev == $past(async_sync)) &&
      (sync_out       == $past(async_sync)) &&
      (sync_out       == async_sync_prev)
  ) else $error("Synchronizer pipeline mismatch");

  // Stage 1 DFF: async_sync samples async_in each cycle
  a_stage1_dff: assert property (async_sync == $past(async_in))
    else $error("Stage1 must sample async_in on each rising edge");

  // No X/Z after pipeline fills (ignore first two clocks)
  a_no_x_after_fill: assert property ($past(1'b1,2) |-> !$isunknown({async_sync, async_sync_prev, sync_out}))
    else $error("X/Z detected on synchronizer state after fill");

  // Output only changes due to prior stage1 change (no spurious toggles)
  a_out_change_has_cause: assert property ($changed(sync_out) |-> $past($changed(async_sync)))
    else $error("sync_out changed without prior stage1 change");

  // Latency coverage: as-implemented, 1-cycle from sampled async_in to sync_out
  c_rise_1cyc: cover property ($rose(async_in) ##1 $rose(sync_out));
  c_fall_1cyc: cover property ($fell(async_in) ##1 $fell(sync_out));

  // Redundancy note: 'if (clk_in)' inside @(posedge clk_in) is always true; else-path unreachable.
  // (Optional) trivial assertion to highlight this:
  a_clk_high_at_posedge: assert property (clk_in);
endmodule

bind synchronizer synchronizer_sva sva_inst();