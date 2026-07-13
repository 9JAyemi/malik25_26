// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): src_rdy_rise_valid_fall, assert, property, posedge, disable, iff, rose, fell, src_rdy_fall_valid_rise, eof_rise_last_fall, eof_fall_last_rise, tready_rise_ll_dst_fall, tready_fall_ll_dst_rise
bind ll_axis_bridge ll_axis_bridge_sva auto_sva_inst (
    .ll_dst_rdy_out_n(ll_dst_rdy_out_n),
    .axis_tready(axis_tready),
    .clk(clk),
    .rst(rst),
    .ll_src_rdy_in_n(ll_src_rdy_in_n),
    .axis_tvalid(axis_tvalid),
    .ll_eof_in_n(ll_eof_in_n),
    .axis_tlast(axis_tlast)
);
