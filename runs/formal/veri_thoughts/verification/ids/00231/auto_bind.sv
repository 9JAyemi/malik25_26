// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_data_out, assert, property, posedge, b0, check_shift_mode_updates_full_register, disable, iff, past, check_load_mode_updates_full_register, check_upper_bits_always_shift, b1, check_shift_mode_inserts_zero, check_load_mode_captures_shift_in
bind shift_register shift_register_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .shift_in(shift_in),
    .shift(shift),
    .data_out(data_out)
);
