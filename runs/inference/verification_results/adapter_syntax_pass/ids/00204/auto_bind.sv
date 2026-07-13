// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_debounced_matches_shift_reg, assert, property, check_zero_shift_reg_drives_low, check_nonzero_shift_reg_drives_high, check_high_output_requires_nonzero_shift_reg, check_low_output_requires_zero_shift_reg
bind debounce debounce_sva auto_sva_inst (
    .pb_debounced(pb_debounced),
    .pb(pb),
    .clk(clk),
    .shift_reg(shift_reg),
    .posedge(posedge),
    .b0000(b0000),
    .b0(b0),
    .b1(b1)
);
