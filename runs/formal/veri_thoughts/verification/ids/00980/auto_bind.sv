// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): past_valid, always, posedge, or, begin, if, b0, else, b1, end, check_load_updates_data_out, assert, property, disable, iff, past, check_load_priority_over_shifts, check_shift_left_updates, check_shift_left_inserts_zero_lsb, check_shift_left_moves_upper_bits, check_shift_right_updates, check_shift_right_inserts_zero_msb, check_shift_right_moves_lower_bits, check_shift_conflict_left_wins, check_hold_when_idle
bind shift_reg shift_reg_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .load(load),
    .shift_left(shift_left),
    .shift_right(shift_right),
    .data_in(data_in),
    .data_out(data_out)
);
