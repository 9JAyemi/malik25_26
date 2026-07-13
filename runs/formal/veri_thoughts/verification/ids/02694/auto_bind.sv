// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_in_ready_passthrough, assert, property, posedge, disable, iff, check_out_data_passthrough, check_out_sop_passthrough, check_out_eop_passthrough, check_out_valid_block_when_channel_gt0, d0, b0, check_out_valid_follow_when_channel_0, check_out_valid_high_implies_inputs, b1, check_out_valid_high_when_allowed, check_out_valid_low_when_not_valid
bind lab3_master_0_b2p_adapter lab3_master_0_b2p_adapter_sva auto_sva_inst (
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
