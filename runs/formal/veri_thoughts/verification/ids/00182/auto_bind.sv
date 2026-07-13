// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): assign, check_reset_clears_qp_flag, assert, property, posedge, b0, check_unmodified_copies_high_left_qp, disable, iff, b1, check_unmodified_copies_low_left_qp, check_modified_block_clears_qp_flag, check_registered_update_function, past
bind db_qp db_qp_sva auto_sva_inst (
    .clk(clk),
    .rst_n(rst_n),
    .cbf_4x4_i(cbf_4x4_i),
    .cbf_u_4x4_i(cbf_u_4x4_i),
    .cbf_v_4x4_i(cbf_v_4x4_i),
    .qp_left_i(qp_left_i),
    .qp_flag_o(qp_flag_o),
    .modified_flag(modified_flag)
);
