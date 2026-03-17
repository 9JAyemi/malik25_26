// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_outputs_zero, assert, property, posedge, b0, valid_next_high_when_p2k_valid, disable, iff, b1, valid_next_low_when_no_p2k_valid, metadata_mode1_ingress0_content, metadata_mode1_ingressnz_content, metadata_mode0_truncated_eid, metadata_holds_when_no_valid, past, mode1_low81_zero, mode1_carries_ingress_bits, mode0_low56_zero
bind key_gen key_gen_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .p2k_valid(p2k_valid),
    .p2k_ingress(p2k_ingress),
    .p2k_rloc_src(p2k_rloc_src),
    .p2k_eid_dst(p2k_eid_dst),
    .p2k_metadata(p2k_metadata),
    .mode(mode),
    .k2m_metadata_valid(k2m_metadata_valid),
    .k2m_metadata(k2m_metadata)
);
