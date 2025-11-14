// SVA for processor_system_reset
// Binds to DUT and checks functional equivalence, X-free outputs, and basic coverage.

module processor_system_reset_sva (
  input slowest_sync_clk,
  input ext_reset_in,
  input aux_reset_in,
  input mb_debug_sys_rst,
  input dcm_locked,
  input mb_reset,
  input [0:0] bus_struct_reset,
  input [0:0] peripheral_reset,
  input [0:0] interconnect_aresetn,
  input [0:0] peripheral_aresetn
);
  default clocking cb @(posedge slowest_sync_clk); endclocking
  // Don’t check while driving condition is unknown
  default disable iff ($isunknown({ext_reset_in, aux_reset_in, mb_debug_sys_rst, dcm_locked}));

  let reset_cond = (ext_reset_in || aux_reset_in || mb_debug_sys_rst || !dcm_locked);
  let outs = {mb_reset, bus_struct_reset[0], peripheral_reset[0], interconnect_aresetn[0], peripheral_aresetn[0]};

  // Outputs must match reset condition bit-for-bit every cycle.
  assert property (outs == {5{reset_cond}})
    else $error("Outputs not equal to reset condition");

  // Outputs must be 0/1 (no X/Z) when inputs are known.
  assert property (!$isunknown(outs))
    else $error("Outputs contain X/Z");

  // If driving inputs are stable, outputs must be stable (no spurious toggles).
  assert property ($stable({ext_reset_in, aux_reset_in, mb_debug_sys_rst, dcm_locked}) |=> $stable(outs))
    else $error("Outputs changed without input change");

  // Coverage: see both assertion and deassertion of reset condition.
  cover property ($rose(reset_cond));
  cover property ($fell(reset_cond));

  // Coverage: dcm_locked gating alone asserts resets.
  cover property ((!dcm_locked && !ext_reset_in && !aux_reset_in && !mb_debug_sys_rst) && (outs == 5'b11111));

  // Coverage: fully released when PLL locked and all resets deasserted.
  cover property (( dcm_locked && !ext_reset_in && !aux_reset_in && !mb_debug_sys_rst) && (outs == 5'b00000));
endmodule

bind processor_system_reset processor_system_reset_sva sva_i (
  .slowest_sync_clk(slowest_sync_clk),
  .ext_reset_in(ext_reset_in),
  .aux_reset_in(aux_reset_in),
  .mb_debug_sys_rst(mb_debug_sys_rst),
  .dcm_locked(dcm_locked),
  .mb_reset(mb_reset),
  .bus_struct_reset(bus_struct_reset),
  .peripheral_reset(peripheral_reset),
  .interconnect_aresetn(interconnect_aresetn),
  .peripheral_aresetn(peripheral_aresetn)
);