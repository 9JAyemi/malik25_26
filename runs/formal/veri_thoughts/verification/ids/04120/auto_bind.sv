// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_in_ready_passthrough, assert, property, posedge, disable, iff, check_out_data_passthrough, check_out_startofpacket_passthrough, check_out_endofpacket_passthrough, check_out_valid_passthrough_channel_zero, h00, check_out_valid_blocked_nonzero_channel, b0
bind soc_system_hps_only_master_b2p_adapter soc_system_hps_only_master_b2p_adapter_sva auto_sva_inst (
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
