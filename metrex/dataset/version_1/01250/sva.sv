// SVA for video_sys_CPU_nios2_performance_monitors
// Bind into DUT to access internals
bind video_sys_CPU_nios2_performance_monitors video_sys_CPU_nios2_performance_monitors_sva sva();

module video_sys_CPU_nios2_performance_monitors_sva;

  // Use DUT scope signals directly via bind
  // clk, reset, inst, stall, ipc, cpi, inst_count, cycle_count, stalled_cycle_count

  // Clocking
  default clocking cb @(posedge clk); endclocking

  // Reset clears all state and outputs by the next cycle
  assert property (reset |=> inst_count==32'd0 && cycle_count==32'd0 &&
                            stalled_cycle_count==32'd0 && ipc==32'd0 && cpi==32'd0);

  // Monotonic counter behavior (mod-2^32 arithmetic)
  assert property (disable iff (reset) inst_count  == $past(inst_count)  + 32'd1);
  assert property (disable iff (reset) cycle_count == $past(cycle_count) + 32'd1);

  // Stalled cycle counter updates only on stall
  assert property (disable iff (reset)  stall |=> stalled_cycle_count == $past(stalled_cycle_count) + 32'd1);
  assert property (disable iff (reset) !stall |=> stalled_cycle_count == $past(stalled_cycle_count));

  // Basic invariants
  assert property (disable iff (reset) inst_count == cycle_count);
  assert property (disable iff (reset) stalled_cycle_count <= cycle_count);

  // Derived "active (non-stalled) cycles" progression
  assert property (disable iff (reset)  stall |=> (cycle_count - stalled_cycle_count) == $past(cycle_count - stalled_cycle_count));
  assert property (disable iff (reset) !stall |=> (cycle_count - stalled_cycle_count) == $past(cycle_count - stalled_cycle_count) + 32'd1);

  // IPC computation from prior-cycle counters
  // denom_past = $past(cycle_count - stalled_cycle_count)
  assert property (disable iff (reset)
                   ($past(cycle_count) - $past(stalled_cycle_count)) == 32'd0
                   |=> ipc == 32'd0);
  assert property (disable iff (reset)
                   ($past(cycle_count) - $past(stalled_cycle_count)) != 32'd0
                   |=> ipc == ($past(inst_count) / ($past(cycle_count) - $past(stalled_cycle_count))));

  // CPI computation from prior-cycle counters
  assert property (disable iff (reset)
                   $past(inst_count) == 32'd0
                   |=> cpi == 32'd0);
  assert property (disable iff (reset)
                   $past(inst_count) != 32'd0
                   |=> cpi == (($past(cycle_count) - $past(stalled_cycle_count)) / $past(inst_count)));

  // Minimal, meaningful coverage
  cover property (reset ##1 !reset);                                   // reset release
  cover property (disable iff (reset) stall[*2]);                      // consecutive stalls
  cover property (disable iff (reset) !stall ##1 stall ##1 !stall);    // stall transition
  cover property (disable iff (reset)
                  ($past(cycle_count) - $past(stalled_cycle_count)) == 32'd0 ##1 ipc == 32'd0); // ipc zero-branch
  cover property (disable iff (reset) ipc != 32'd0);                   // non-zero ipc observed
  cover property (disable iff (reset) cpi != 32'd0);                   // non-zero cpi observed

endmodule