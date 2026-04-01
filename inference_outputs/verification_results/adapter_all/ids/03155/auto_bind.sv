// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_s1_out_registered_sum, assert, property, disable, iff, b1, past, b0, check_s2_out_registered_sum, check_s1_out_matches_registered_path, b00, check_s2_out_matches_registered_path, check_s1_out_independent_of_s2, check_s2_out_independent_of_s1, check_s1_out_stable_when_cos_and_s1_stable, check_s2_out_stable_when_cos_and_s2_stable, check_s1_out_changes_only_with_s2, check_s2_out_changes_only_with_s1
bind math_ops math_ops_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .cos(cos),
    .one(one),
    .s1(s1),
    .s2(s2),
    .s1_out(s1_out),
    .s2_out(s2_out),
    .posedge(posedge)
);
