// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_round_flag_truth_table, assert, property, global_clock, b1, b01, b0, b10, b00, check_zero_data_clears_flag, check_sign1_round01_nonzero_sets_flag, check_sign0_round10_nonzero_sets_flag, check_flag_requires_nonzero_data, check_sign1_flag_only_in_round01, check_sign0_flag_only_in_round10, check_unused_round_types_clear_flag, b11, check_sign1_round10_clears_flag, check_sign0_round01_clears_flag
bind Round_Sgf_Dec Round_Sgf_Dec_sva auto_sva_inst (
    .Data_i(Data_i),
    .Round_Type_i(Round_Type_i),
    .Sign_Result_i(Sign_Result_i),
    .Round_Flag_o(Round_Flag_o)
);
