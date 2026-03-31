// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_q, assert, property, h0, check_reset_clears_shifted_q, check_subbed_a_difference, disable, iff, check_added_a_select, check_result_mux, check_result_sub_mode, check_result_add_mode, check_reset_subbed_a_value, check_reset_result_value, check_b_unused, changed, stable, check_ser_unused
bind shift_addsub shift_addsub_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .SER(SER),
    .A(A),
    .B(B),
    .sub(sub),
    .result(result),
    .Q(Q),
    .shifted_Q(shifted_Q),
    .added_A(added_A),
    .subbed_A(subbed_A),
    .posedge(posedge)
);
