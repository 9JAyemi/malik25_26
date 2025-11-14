// SVA for reset_module — concise, quality-focused
// Bind these assertions to the DUT. They check internal state update,
// output behavior, gating by dcm_locked/aux_reset, and cover key scenarios.

module reset_module_sva (
  input logic slowest_clk,
  input logic ext_reset,
  input logic aux_reset,
  input logic dcm_locked,
  input logic debug_sys_rst,
  input logic sys_reset,
  input logic [0:0] bus_struct_reset,
  input logic [0:0] peripheral_reset,
  input logic [0:0] interconnect_reset,
  input logic [0:0] peripheral_aresetn,
  input logic [1:0] reset_state,
  input logic [1:0] sync_reset_state
);

  default clocking cb @(posedge slowest_clk); endclocking

  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge slowest_clk) past_valid <= 1'b1;

  // Sanity: no X/Z after first cycle
  assert property (disable iff (!past_valid)
    !$isunknown({sys_reset,
                 bus_struct_reset[0], peripheral_reset[0],
                 interconnect_reset[0], peripheral_aresetn[0],
                 reset_state, sync_reset_state}));

  // 2-flop sync: sync_reset_state is previous reset_state
  assert property (disable iff (!past_valid)
    sync_reset_state == $past(reset_state));

  // reset_state[0] update when locked, hold when not locked
  assert property (disable iff (!past_valid)
    $past(dcm_locked) |-> reset_state[0] == ~$past(ext_reset));
  assert property (disable iff (!past_valid)
    !$past(dcm_locked) |-> reset_state[0] == $past(reset_state[0]));

  // reset_state[1] next-state function and hold when not locked
  assert property (disable iff (!past_valid)
    $past(dcm_locked) |-> reset_state[1] ==
      ($past(reset_state[0]) & (~$past(aux_reset) | $past(sync_reset_state[1]))));
  assert property (disable iff (!past_valid)
    !$past(dcm_locked) |-> reset_state[1] == $past(reset_state[1]));

  // Outputs equal functions of previous-cycle inputs (due to NBA ordering)
  assert property (disable iff (!past_valid)
    sys_reset == ($past(debug_sys_rst) || $past(sync_reset_state[1])));
  assert property (disable iff (!past_valid)
    bus_struct_reset[0] == $past(sync_reset_state[1]) &&
    peripheral_reset[0] == $past(sync_reset_state[1]) &&
    interconnect_reset[0] == $past(sync_reset_state[1]));
  assert property (disable iff (!past_valid)
    peripheral_aresetn[0] == ~ $past(sync_reset_state[1]));

  // Consistency relations among outputs
  assert property (bus_struct_reset[0] == peripheral_reset[0] &&
                   bus_struct_reset[0] == interconnect_reset[0]);
  assert property (peripheral_aresetn[0] == ~peripheral_reset[0]);

  // If any fabric reset is asserted, sys_reset must be asserted
  assert property (bus_struct_reset[0] |-> sys_reset);
  assert property (peripheral_reset[0]  |-> sys_reset);
  assert property (interconnect_reset[0]|-> sys_reset);
  assert property ((!peripheral_aresetn[0]) |-> sys_reset);

  // Debug reset does not drive fabric resets
  assert property (disable iff (!past_valid)
    $past(debug_sys_rst) && !$past(sync_reset_state[1]) |->
      !(bus_struct_reset[0] || peripheral_reset[0] || interconnect_reset[0]));

  // Coverage: lock acquisition
  cover property (past_valid && !$past(dcm_locked) ##1 dcm_locked);

  // Coverage: external reset path asserts fabric resets (aux allows)
  cover property (past_valid &&
                  dcm_locked && !ext_reset && !aux_reset
                  ##2 (bus_struct_reset[0] && peripheral_reset[0] &&
                       interconnect_reset[0] && !peripheral_aresetn[0]));

  // Coverage: debug-only reset (fabric resets stay low)
  cover property (past_valid &&
                  $rose(debug_sys_rst) ##1
                  (sys_reset && !(bus_struct_reset[0] || peripheral_reset[0] || interconnect_reset[0])));

  // Coverage: deassertion of resets when ext_reset deasserts (locked)
  cover property (past_valid && dcm_locked && ext_reset
                  ##2 (!bus_struct_reset[0] && !peripheral_reset[0] &&
                       !interconnect_reset[0] && peripheral_aresetn[0]));

endmodule

// Bind into the DUT; internal regs are connected for assertion visibility
bind reset_module reset_module_sva
  sva_i (.*,
         .reset_state(reset_state),
         .sync_reset_state(sync_reset_state));