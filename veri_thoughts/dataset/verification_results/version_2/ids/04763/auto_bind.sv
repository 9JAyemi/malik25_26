// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_shifted_data, assert, property, posedge, h00000000, check_reset_clears_zero_flag, b0, check_shifted_data_update, disable, iff, b1, past, check_zero_flag_set_on_zero_input, check_zero_flag_clear_on_nonzero_input
bind shift_and_check shift_and_check_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .input_data(input_data),
    .shifted_data(shifted_data),
    .zero_flag(zero_flag)
);
