// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_out_matches_neq, assert, property, posedge, check_out_matches_xor_or, check_next_state_function, b1, past, b00, check_load_updates_from_data, check_shift_when_ena_nonzero, check_hold_when_idle, check_shift_upper_bits, check_shift_lower_bits, check_q_changes_only_when_allowed, check_out_stable_if_inputs_stable, stable
bind xor_shift_register xor_shift_register_sva auto_sva_inst (
    .clk(clk),
    .load(load),
    .ena(ena),
    .data(data),
    .q(q),
    .out_if_else(out_if_else)
);
