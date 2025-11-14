// SVA checker for ip_design_rst_ps7_0_100M_0
// Notes: Per RTL, all outputs are active-HIGH resets (including *_aresetn).
module ip_design_rst_ps7_0_100M_0_sva (
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

  logic past_valid;
  always @(posedge slowest_sync_clk) past_valid <= 1'b1;

  wire reset_req = ext_reset_in || aux_reset_in || mb_debug_sys_rst || !dcm_locked;

  // Functional equivalence: every output matches reset condition
  property p_outputs_match_inputs;
    reset_req == mb_reset
    && reset_req == bus_struct_reset[0]
    && reset_req == peripheral_reset[0]
    && reset_req == interconnect_aresetn[0]
    && reset_req == peripheral_aresetn[0];
  endproperty

  assert property (disable iff (!past_valid) p_outputs_match_inputs)
    else $error("Outputs must equal ext|aux|dbg|!locked");

  // Outputs must never be X/Z after first observed clock
  assert property (disable iff (!past_valid)
                   !$isunknown({mb_reset,
                                bus_struct_reset[0],
                                peripheral_reset[0],
                                interconnect_aresetn[0],
                                peripheral_aresetn[0]}))
    else $error("Unknown value on reset outputs");

  // Optional edge-consistency: any change in reset_req reflects on outputs the same cycle
  assert property (disable iff (!past_valid)
                   $changed(reset_req) |-> $changed({mb_reset,
                                                     bus_struct_reset[0],
                                                     peripheral_reset[0],
                                                     interconnect_aresetn[0],
                                                     peripheral_aresetn[0]}))
    else $error("Outputs must change iff reset condition changes");

  // ----------------------------------------------------------------------------
  // Coverage
  // ----------------------------------------------------------------------------
  // Each independent reset source (with others idle and clock locked)
  cover property (disable iff (!past_valid)
                  ext_reset_in && !aux_reset_in && !mb_debug_sys_rst && dcm_locked);
  cover property (disable iff (!past_valid)
                  aux_reset_in && !ext_reset_in && !mb_debug_sys_rst && dcm_locked);
  cover property (disable iff (!past_valid)
                  mb_debug_sys_rst && !ext_reset_in && !aux_reset_in && dcm_locked);

  // Loss of lock alone triggers reset
  cover property (disable iff (!past_valid)
                  !dcm_locked && !ext_reset_in && !aux_reset_in && !mb_debug_sys_rst);

  // Release condition: all inputs idle and lock good -> outputs deassert
  cover property (disable iff (!past_valid)
                  reset_req ##1 !reset_req);      // 1->0 transition
  cover property (disable iff (!past_valid)
                  !reset_req ##1 reset_req ##1 !reset_req); // pulse reset

  // Observe output edges
  cover property (disable iff (!past_valid) $rose(mb_reset));
  cover property (disable iff (!past_valid) $fell(mb_reset));

endmodule

// Bind into DUT
bind ip_design_rst_ps7_0_100M_0 ip_design_rst_ps7_0_100M_0_sva u_ip_design_rst_ps7_0_100M_0_sva (
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