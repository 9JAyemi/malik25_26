// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): data, check_reset_clears_state, assert, property, posedge, disable, iff, past, h0, b0, check_shift_updates_data, check_shift_updates_shift_out, check_hold_data_without_shift, check_hold_shiftout_without_shift, check_data_msb_from_prev_bit14, check_data_lsb_from_shiftin, check_reset_overrides_shift
bind shift_register shift_register_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .shift_in(shift_in),
    .shift(shift),
    .shift_out(shift_out)
);
