// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_s_captures_upper_nibble, assert, property, posedge, past, check_s_holds_without_awvalid, check_q_captures_bit39_on_change, check_q_holds_without_change, check_awaddr_increments_when_nonzero, h000, check_awaddr_holds_when_zero, check_wrap_second_len_captures_on_state1_change, check_wrap_second_len_holds_without_state1_change, check_next_pending_captures_on_next_change, check_next_pending_holds_without_next_change
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
