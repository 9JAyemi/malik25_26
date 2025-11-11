// SVA for axis_counter
// Bind into the DUT; assertions reference DUT internals for precise checking

module axis_counter_sva
  #(parameter int AXIS_TDATA_WIDTH = 32,
    parameter int CNTR_WIDTH       = 32);

  // These names resolve in the bound scope (axis_counter)
  // clocking and global reset gating
  default clocking cb @(posedge aclk); endclocking
  default disable iff (!aresetn);

  // Known/clean outputs after reset deassertion
  ap_no_x_outputs: assert property (!$isunknown({m_axis_tvalid, m_axis_tdata})));

  // Synchronous reset behavior (checked during reset)
  ap_sync_reset: assert property (!aresetn |-> (int_cntr_reg == '0 && int_enbl_reg == 1'b0 && m_axis_tvalid == 1'b0));

  // Basic combinational definitions
  ap_comp_def:     assert property (int_comp_wire == (int_cntr_reg < cfg_data));
  ap_valid_mapping:assert property (m_axis_tvalid == int_enbl_reg);

  // TDATA zero-extension mapping
  ap_tdata_low:    assert property (m_axis_tdata[CNTR_WIDTH-1:0] == int_cntr_reg);
  generate if (AXIS_TDATA_WIDTH > CNTR_WIDTH) begin : g_hi_zero
    ap_tdata_high_zero: assert property (m_axis_tdata[AXIS_TDATA_WIDTH-1:CNTR_WIDTH] == '0);
  end endgenerate

  // Enable tracks comparison one cycle later
  ap_enbl_tracks_comp: assert property ($past(aresetn) |-> (int_enbl_reg == $past(int_comp_wire)));

  // Counter next-state: increment iff previously enabled and comp was true; else hold
  ap_counter_nx: assert property (
    $past(aresetn) |-> int_cntr_reg == $past(int_cntr_reg) + ($past(int_enbl_reg & int_comp_wire) ? 1 : 0)
  );

  // Monotonic non-decreasing (lightweight safety)
  ap_counter_monotonic: assert property ($past(aresetn) |-> (int_cntr_reg >= $past(int_cntr_reg)));

  // Functional coverage

  // Normal run: enable rises then eventually falls at terminal count (counter equals cfg_data)
  cp_start_stop: cover property (
    (cfg_data > 0) ##1 $rose(int_enbl_reg) ##[1:$] ($fell(int_enbl_reg) && (int_cntr_reg == cfg_data))
  );

  // At least one increment step occurs while enabled
  cp_increment: cover property ($past(int_enbl_reg & int_comp_wire) && (int_cntr_reg == $past(int_cntr_reg) + 1));

  // cfg_data == 0 corner: never enables and counter holds at 0
  cp_cfg_zero: cover property ((cfg_data == 0) ##1 (!int_enbl_reg && int_cntr_reg == '0) ##1 (!int_enbl_reg && int_cntr_reg == '0));

  // Dynamic cfg drop while counting: immediate disable without increment
  cp_cfg_drop_disables: cover property (
    $past(int_enbl_reg & int_comp_wire) && !int_comp_wire && !int_enbl_reg && (int_cntr_reg == $past(int_cntr_reg))
  );

  // Dynamic cfg raise from disabled: immediate enable without increment
  cp_cfg_raise_enables: cover property (
    $past(!int_enbl_reg && !int_comp_wire) && int_comp_wire && int_enbl_reg && (int_cntr_reg == $past(int_cntr_reg))
  );

endmodule

// Bind into the DUT
bind axis_counter axis_counter_sva #(.AXIS_TDATA_WIDTH(AXIS_TDATA_WIDTH),
                                     .CNTR_WIDTH(CNTR_WIDTH)) u_axis_counter_sva();