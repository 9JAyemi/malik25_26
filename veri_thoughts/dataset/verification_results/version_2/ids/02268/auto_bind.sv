// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_status_constant_value, assert, property, posedge, h000000A0, check_status_stable_over_time, disable, iff, initstate, past, check_src_enable_registered_from_dst_enable, check_src_valid_registered_from_dst_valid, check_dst_data_registered_from_src_data, check_src_enable_stable_when_dst_enable_stable, check_src_valid_stable_when_dst_valid_stable, check_dst_data_stable_when_src_data_stable
bind prcfg_dac prcfg_dac_sva auto_sva_inst (
    .clk(clk),
    .control(control),
    .status(status),
    .src_dac_enable(src_dac_enable),
    .src_dac_data(src_dac_data),
    .src_dac_valid(src_dac_valid),
    .dst_dac_enable(dst_dac_enable),
    .dst_dac_data(dst_dac_data),
    .dst_dac_valid(dst_dac_valid)
);
