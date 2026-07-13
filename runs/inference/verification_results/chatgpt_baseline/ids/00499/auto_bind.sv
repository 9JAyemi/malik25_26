// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_q, assert, property, posedge, disable, iff, past, b0000, check_parallel_load_updates_q, check_shift_left_updates_q, b0, check_shift_right_updates_q, check_idle_holds_q, check_parallel_load_priority_over_shifts, check_shift_left_priority_over_shift_right, check_reset_priority_over_controls
bind shift_register shift_register_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .parallel_load(parallel_load),
    .shift_left(shift_left),
    .shift_right(shift_right),
    .parallel_input(parallel_input),
    .q(q)
);
