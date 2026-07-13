// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_outputs_low, assert, property, posedge, b0, check_nfl_num_toggle_each_cycle, disable, iff, past, b1, check_nfl_num_always_changes, changed, check_inc_dec_b_captures_prev_nand, check_inc_dec_b_change_matches_prev_input_change, check_inc_dec_b_no_change_if_prev_input_nand_unchanged, check_inc_dec_b_zero_only_on_prev_both_high, check_inc_dec_b_one_on_prev_not_both_high
bind errman_nfl errman_nfl_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .cfg_err_cpl_timeout_n(cfg_err_cpl_timeout_n),
    .decr_nfl(decr_nfl),
    .nfl_num(nfl_num),
    .inc_dec_b(inc_dec_b)
);
