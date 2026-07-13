// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_in_ready_passthrough, assert, property, posedge, disable, iff, check_out_data_passthrough, check_out_sop_passthrough, check_out_eop_passthrough, check_valid_masked_when_channel_high, h0F, b0, check_valid_follows_input_when_channel_ok, check_out_valid_implies_in_valid, check_out_valid_implies_channel_in_range, check_in_valid_low_forces_out_valid_low, check_drop_only_due_to_channel, check_valid_logic_equivalence
bind soc_system_master_secure_b2p_adapter soc_system_master_secure_b2p_adapter_sva auto_sva_inst (
    .clk(clk),
    .reset_n(reset_n),
    .in_ready(in_ready),
    .in_valid(in_valid),
    .in_data(in_data),
    .in_channel(in_channel),
    .in_startofpacket(in_startofpacket),
    .in_endofpacket(in_endofpacket),
    .out_ready(out_ready),
    .out_valid(out_valid),
    .out_data(out_data),
    .out_startofpacket(out_startofpacket),
    .out_endofpacket(out_endofpacket)
);
