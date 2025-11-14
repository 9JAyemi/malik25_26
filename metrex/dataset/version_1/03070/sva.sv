// SVA for soc_system_hps_only_master_b2p_adapter
// Bind this checker to the DUT

module soc_system_hps_only_master_b2p_adapter_sva;
  // The bound scope is the DUT instance; we can directly reference its signals
  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n);

  // Core functional relations
  ap_ready_passthru:     assert property (in_ready == out_ready);
  ap_out_valid_expr:     assert property (out_valid == (in_valid && (in_channel == 8'h00)));
  ap_data_passthru:      assert property (out_data == in_data);
  ap_sop_passthru:       assert property (out_startofpacket == in_startofpacket);
  ap_eop_passthru:       assert property (out_endofpacket == in_endofpacket);

  // Illegal/robustness checks
  ap_out_valid_implies_ch0: assert property (out_valid |-> (in_channel == 8'h00));
  ap_no_x_on_outputs:       assert property (!$isunknown({in_ready, out_valid, out_startofpacket, out_endofpacket, out_data}));

  // Internal channel assignment (width truncation) behavior
  ap_internal_channel_trunc: assert property (out_channel == in_channel[0]);
  ap_valid_only_when_upper_zero: assert property (out_valid |-> (in_channel[7:1] == '0));

  // Coverage
  cp_allow_ch0:     cover property (in_valid && (in_channel == 8'h00) && out_valid);
  cp_block_nonzero: cover property (in_valid && (in_channel != 8'h00) && !out_valid);
  cp_sop_seen:      cover property (out_valid && out_startofpacket);
  cp_eop_seen:      cover property (out_valid && out_endofpacket);
  cp_upper_bits_exercised: cover property (in_channel[7:1] != '0);
  cp_ready_passthru: cover property (in_ready && out_ready);
endmodule

bind soc_system_hps_only_master_b2p_adapter soc_system_hps_only_master_b2p_adapter_sva sva_i;