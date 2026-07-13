// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): MAX_CHANNEL, d15, check_in_ready_passthrough, assert, property, posedge, disable, iff, check_data_passthrough, check_sop_passthrough, check_eop_passthrough, check_out_valid_definition, check_outputs_stable_when_inputs_stable, stable, check_out_valid_independent_of_out_ready, changed, check_out_valid_independent_of_payload_ctrl, check_out_valid_rise_tracks_in_valid, rose, past, check_out_valid_fall_tracks_in_valid, fell
bind data_adapter data_adapter_sva auto_sva_inst (
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
