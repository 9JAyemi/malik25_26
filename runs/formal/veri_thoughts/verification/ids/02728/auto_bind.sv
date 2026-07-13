// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): internal_state, reset_clears_regs, assert, property, posedge, h0, key_zero_passthrough, disable, iff, hold_internal_state_when_key_zero, past, update_internal_state_when_key_nonzero, data_out_uses_prev_internal_state_when_key_nonzero, first_nonzero_key_after_reset_outputs_key, internal_state_matches_prev_calc_on_key_drop_to_zero, data_out_two_cycle_relation_when_key_nonzero_consecutive
bind mem_encryption mem_encryption_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .data_in(data_in),
    .key(key),
    .data_out(data_out)
);
