// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): CLK, fwd1_from_m_when_match, assert, property, posedge, disable, iff, b0, h1, fwd1_from_w_when_no_m_but_w_match, h2, fwd1_none_when_no_matches, h0, fwd1_encoding_valid, b1, h3, fwd2_from_m_when_match, fwd2_from_w_when_no_m_but_w_match, fwd2_none_when_no_matches, fwd2_encoding_valid, stalls_equal, stall_equals_flush_e, flush_d_equals_PC_source, no_hazard_results_no_stall_or_flush_e, hazard_and_memtoreg_cause_stall_and_flush_e, memtoreg_low_clears_stall_and_flush_e
bind hazard hazard_sva auto_sva_inst (
    .reg_read_adr1_d(reg_read_adr1_d),
    .reg_read_adr2_d(reg_read_adr2_d),
    .reg_read_adr1_e(reg_read_adr1_e),
    .reg_read_adr2_e(reg_read_adr2_e),
    .reg_write_adr_e(reg_write_adr_e),
    .mem_to_reg_e(mem_to_reg_e),
    .reg_write_m(reg_write_m),
    .reg_write_adr_m(reg_write_adr_m),
    .reg_write_w(reg_write_w),
    .reg_write_adr_w(reg_write_adr_w),
    .PC_source(PC_source),
    .stall_f(stall_f),
    .stall_d(stall_d),
    .flush_d(flush_d),
    .flush_e(flush_e),
    .forward1_e(forward1_e),
    .forward2_e(forward2_e)
);
