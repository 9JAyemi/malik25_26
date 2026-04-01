// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_q, assert, property, b0000, check_reset_priority_over_load, check_reset_priority_over_enable, check_reset_priority_over_both, check_load_captures_data, disable, iff, check_enable_shifts_q, past, check_hold_when_idle, check_load_priority_over_enable, check_shift_after_load
bind shift_register shift_register_sva auto_sva_inst (
    .clk(clk),
    .areset(areset),
    .load(load),
    .ena(ena),
    .data(data),
    .q(q),
    .posedge(posedge),
    .b0(b0)
);
