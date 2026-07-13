// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_load_captures_data, assert, property, posedge, past, check_hold_when_not_loading, check_rotate_when_enabled, b00, check_hold_when_enabled, check_out_if_else_high_when_q_differs_from_data, b1, check_out_if_else_low_when_q_matches_data, b0
bind xor_shift_register xor_shift_register_sva auto_sva_inst (
    .clk(clk),
    .load(load),
    .ena(ena),
    .data(data),
    .q(q),
    .out_if_else(out_if_else)
);
