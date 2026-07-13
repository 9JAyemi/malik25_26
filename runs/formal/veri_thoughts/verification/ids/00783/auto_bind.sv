// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_q_equals_q_ff2, assert, property, check_qff1_stable_on_posedge, past, b1, stable, check_qff2_stable_on_posedge, check_q_stable_on_posedge, check_ff1_negedge_samples_prior_posedge_d, check_ff2_negedge_samples_prior_posedge_qff1, check_top_negedge_matches_d_two_posedges_ago
bind dual_edge_triggered_ff top_module_sva auto_sva_inst (
    .clk(clk),
    .d(d),
    .q(q),
    .q_ff1(q_ff1),
    .q_ff2(q_ff2),
    .posedge(posedge),
    .negedge(negedge)
);
