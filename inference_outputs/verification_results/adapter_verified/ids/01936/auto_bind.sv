// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_load_captures_data, assert, property, posedge, past, check_rotate_when_ena_nonzero, disable, iff, b00, check_hold_when_ena_zero, check_out_if_else_matches_xor, check_out_if_else_high_after_load, b1, check_out_if_else_low_on_rotate, b0, check_out_if_else_high_on_hold
bind xor_shift_register xor_shift_register_sva auto_sva_inst (
    .clk(clk),
    .load(load),
    .ena(ena),
    .data(data),
    .q(q),
    .out_if_else(out_if_else)
);
