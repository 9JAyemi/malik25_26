// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): ready_pulse_single_cycle, assert, property, posedge, rose, payload_update_only_when_ready, changed, b1, payload_no_update_when_ready_low, b0, payload_no_back_to_back_updates, payload_update_implies_ready_low_next, ready_high_payload_stable_next, stable
bind axi_protocol_converter axi_protocol_converter_sva auto_sva_inst (
    .aclk(aclk),
    .m_axi_arvalid(m_axi_arvalid),
    .m_axi_arready(m_axi_arready),
    .m_axi_araddr(m_axi_araddr),
    .m_payload_i_reg(m_payload_i_reg),
    .m_payload_o_reg(m_payload_o_reg),
    .si_rs_arvalid(si_rs_arvalid)
);
