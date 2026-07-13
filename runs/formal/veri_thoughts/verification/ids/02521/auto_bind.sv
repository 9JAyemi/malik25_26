// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_q, assert, property, posedge, b0000, check_load_updates_q, disable, iff, past, check_priority_load_over_ena, check_shift_left_when_ena_only, b0, check_shift_lsb_zero, check_shift_msb_from_bit2, check_shift_bit2_from_bit1, check_shift_bit1_from_bit0, check_hold_when_idle
bind shift_register_left shift_register_left_sva auto_sva_inst (
    .clk(clk),
    .areset_n(areset_n),
    .load(load),
    .ena(ena),
    .data(data),
    .q(q)
);
