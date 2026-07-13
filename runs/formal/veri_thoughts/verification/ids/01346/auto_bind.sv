// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_sel_first_loads, assert, property, posedge, b1, b0, check_sel_first_flag_mirror, check_incr_branch_flags, check_wrap_branch_effects, check_next_branch_effects, check_payload_holds_when_sel_first_low, past, check_addr_holds_when_no_update, check_flags_hold_when_idle
bind axi_to_custom_protocol_converter axi_to_custom_protocol_converter_sva auto_sva_inst (
    .next_pending_r_reg(next_pending_r_reg),
    .m_axi_awaddr(m_axi_awaddr),
    .m_payload_i_reg(m_payload_i_reg),
    .incr_next_pending(incr_next_pending),
    .wrap_next_pending(wrap_next_pending),
    .sel_first_reg_0(sel_first_reg_0),
    .aclk(aclk),
    .m_axi_awaddr_in(m_axi_awaddr_in),
    .m_payload_i_reg_in(m_payload_i_reg_in),
    .next(next),
    .incr_next_pending_in(incr_next_pending_in),
    .wrap_next_pending_in(wrap_next_pending_in),
    .sel_first_i(sel_first_i)
);
