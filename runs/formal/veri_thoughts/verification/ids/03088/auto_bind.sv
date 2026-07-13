// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_outputs, assert, property, posedge, b0, check_load_updates_register, disable, iff, past, check_shift_left_behavior, check_shift_right_behavior, check_idle_holds_register, check_load_priority_over_shifts, check_shift_left_priority_over_shift_right
bind shift_register shift_register_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .parallel_load(parallel_load),
    .load(load),
    .shift_left(shift_left),
    .shift_right(shift_right),
    .q(q),
    .serial_out(serial_out)
);
