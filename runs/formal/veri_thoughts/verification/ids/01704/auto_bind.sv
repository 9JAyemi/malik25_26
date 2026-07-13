// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_dataout18_passthrough, assert, property, disable, iff, check_dataout17_passthrough, check_dataout_lo16_passthrough, check_dataout16_when_17and16_set, b1, check_src_rdy_o_definition, check_src_rdy_o_zero_when_src_not_ready, check_src_rdy_o_zero_when_dst_not_ready, check_dst_rdy_o_implies_handshake, check_dst_rdy_o_subset_src_rdy_o, check_dst_rdy_o_zero_when_src_not_ready, check_dst_rdy_o_zero_when_dst_not_ready
bind fifo19_rxrealign fifo19_rxrealign_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .clear(clear),
    .datain(datain),
    .src_rdy_i(src_rdy_i),
    .dst_rdy_o(dst_rdy_o),
    .dataout(dataout),
    .src_rdy_o(src_rdy_o),
    .dst_rdy_i(dst_rdy_i),
    .posedge(posedge)
);
