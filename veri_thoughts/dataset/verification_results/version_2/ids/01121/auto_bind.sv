// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_input_ready_const_high, assert, property, disable, iff, b1, check_valid_passthrough, check_reset_clears_outputs, h0, b0, check_capture_dest_ip_on_handshake, past, check_dest_ip_stable_without_handshake, check_drop_update_on_handshake, check_drop_stable_without_handshake, check_drop_change_requires_prev_handshake, check_dest_ip_change_requires_prev_handshake, check_eth_mac_stable_post_reset, stable, check_length_stable_post_reset
bind ip_packet_filter ip_packet_filter_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .input_ip_hdr_valid(input_ip_hdr_valid),
    .input_ip_hdr_ready(input_ip_hdr_ready),
    .input_ip_dest_ip(input_ip_dest_ip),
    .output_ip_hdr_valid(output_ip_hdr_valid),
    .output_ip_hdr_ready(output_ip_hdr_ready),
    .output_ip_dest_ip(output_ip_dest_ip),
    .output_ip_eth_dest_mac(output_ip_eth_dest_mac),
    .output_ip_length(output_ip_length),
    .drop(drop),
    .FILTER_IP(FILTER_IP),
    .hc0a80101(hc0a80101),
    .posedge(posedge)
);
