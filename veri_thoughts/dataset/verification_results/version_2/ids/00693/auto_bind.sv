// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_output, assert, property, posedge, b0, load_updates_immediately, disable, iff, rotate_one_step_vector, past, rotate_bit7_from6, rotate_bit0_from7, rotate_eight_cycle_identity, first_cycle_after_reset_no_load_zero, rose, first_cycle_after_reset_with_load_loads
bind shift_register shift_register_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .load(load),
    .data_in(data_in),
    .data_out(data_out)
);
