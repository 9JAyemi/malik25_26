// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_s_capture_on_valid, assert, property, posedge, disable, iff, initstate, past, check_s_hold_without_valid, check_awaddr_increment_on_nonzero_incr, b0, check_awaddr_hold_on_zero_incr, check_q_update_on_payload_bit39_change, check_q_hold_when_payload_bit39_stable, check_wrap_len_update_on_state_bit1_change, b00, check_wrap_len_hold_when_state_bit1_stable, check_next_pending_follow_on_toggle, check_next_pending_high_on_stable_high, b1, check_next_pending_hold_on_stable_low
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
