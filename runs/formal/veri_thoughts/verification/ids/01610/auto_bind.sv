// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_ready_high, assert, property, posedge, b1, check_tvalid_definition, disable, iff, check_tvalid_low_when_s_valid_low, check_tvalid_low_when_not_ready, check_valid_eq_when_ready, check_valid_eq_when_s_valid, check_data_passthrough, check_data_when_valid, check_m_valid_implies_s_valid_and_ready
bind axis_pulse_generator axis_pulse_generator_sva auto_sva_inst (
    .aclk(aclk),
    .aresetn(aresetn),
    .s_axis_tready(s_axis_tready),
    .s_axis_tdata(s_axis_tdata),
    .s_axis_tvalid(s_axis_tvalid),
    .m_axis_tready(m_axis_tready),
    .m_axis_tdata(m_axis_tdata),
    .m_axis_tvalid(m_axis_tvalid)
);
