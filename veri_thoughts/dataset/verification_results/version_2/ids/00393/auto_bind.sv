// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_counter, assert, property, h0, check_counter_increments, disable, iff, hF, past, h1, check_counter_wraps, check_shift_matches_left_shift, check_shift_zero_passthrough, check_shift_fifteen_endpoint, check_shift_nonzero_clears_lsb
bind counter_with_reset top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .data_in(data_in),
    .shift_amt(shift_amt),
    .count_out(count_out),
    .shifted_data(shifted_data),
    .posedge(posedge),
    .b0(b0)
);
