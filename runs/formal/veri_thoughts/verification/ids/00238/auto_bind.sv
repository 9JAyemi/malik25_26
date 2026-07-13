// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_round_flag_exact_decode, assert, property, global_clock, b10101, b10110, b10111, b01001, b01010, b01011, check_type01_positive_nonzero_sets_flag, b1, b01, b10, b11, check_type10_negative_nonzero_sets_flag, b0, check_zero_data_clears_flag, b00, check_round_type00_clears_flag, check_round_type11_clears_flag, check_type01_negative_clears_flag, check_type10_positive_clears_flag, check_flag_high_requires_nonzero_data, check_flag_high_requires_supported_sign_type
bind Round_Sgf_Dec Round_Sgf_Dec_sva auto_sva_inst (
    .Data_i(Data_i),
    .Round_Type_i(Round_Type_i),
    .Sign_Result_i(Sign_Result_i),
    .Round_Flag_o(Round_Flag_o)
);
