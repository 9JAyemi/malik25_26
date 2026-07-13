// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): clk, check_equal_flag, assert, property, posedge, check_signed_larger_flag, check_signed_smaller_flag, check_compare_flags_mutex, check_larger_num_select, check_smaller_num_select, check_shift_right_logical_mode, check_shift_right_arithmetic_mode, check_out_zero_when_equal, b0000, check_out_shifted_when_signed_larger, check_out_smaller_otherwise
bind compare_signed_mag top_module_sva auto_sva_inst (
    .A(A),
    .B(B),
    .shift_amt(shift_amt),
    .mode(mode),
    .out(out),
    .equal(equal),
    .signed_larger(signed_larger),
    .signed_smaller(signed_smaller),
    .larger_num(larger_num),
    .smaller_num(smaller_num),
    .shifted_num(shifted_num)
);
