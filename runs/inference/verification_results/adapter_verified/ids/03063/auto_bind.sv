// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_s_capture, assert, property, posedge, past, check_s_hold, check_next_pending_set, b1, check_next_pending_clear, b0, check_awaddr_increment, h000, check_awaddr_hold, check_q_capture_on_bit39_change, check_q_hold_on_bit39_stable, check_wrap_second_capture_on_state1_change, check_wrap_second_hold_on_state1_stable
bind simplified_axi_protocol_converter simplified_axi_protocol_converter_sva auto_sva_inst (
    .si_rs_awvalid(si_rs_awvalid),
    .m_payload_i_reg(m_payload_i_reg),
    .state_reg(state_reg),
    .axaddr_incr(axaddr_incr),
    .next(next),
    .aclk(aclk),
    .Q(Q),
    .S(S),
    .m_axi_awaddr(m_axi_awaddr),
    .wrap_second_len_r_reg(wrap_second_len_r_reg),
    .next_pending_r_reg(next_pending_r_reg)
);
