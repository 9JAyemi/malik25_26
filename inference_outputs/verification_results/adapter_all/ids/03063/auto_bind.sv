// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_s_captures_m_payload_bits, assert, property, posedge, past, check_s_holds_without_awvalid, check_awaddr_increments_on_nonzero_axaddr_incr, d0, check_awaddr_holds_on_zero_axaddr_incr, check_q_captures_msb_change, check_q_holds_on_msb_stable, check_wrap_second_len_captures_state_change, check_wrap_second_len_holds_on_state_stable, check_next_pending_r_captures_next_change, check_next_pending_r_holds_on_next_stable
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
