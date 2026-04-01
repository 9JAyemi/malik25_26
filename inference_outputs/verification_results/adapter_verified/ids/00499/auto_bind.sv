// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_register, assert, property, posedge, b0000, check_parallel_load_captures_input, disable, iff, past, check_shift_left_behavior, b0, check_shift_right_behavior, check_hold_when_idle, check_shift_left_priority_over_right
bind shift_register shift_register_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .parallel_load(parallel_load),
    .shift_left(shift_left),
    .shift_right(shift_right),
    .parallel_input(parallel_input),
    .q(q)
);
