// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): shift_reg, check_dataout_mirrors_shiftreg, assert, property, posedge, check_next_state_equation, b1, sampled, load_captures_data_in_next_cycle, shift_moves_msb_from_bit2, shift_moves_bit2_from_bit1, shift_moves_bit1_from_bit0, shift_in_captures_into_lsb, two_consecutive_shifts_chain, past, two_consecutive_loads_last_sample_kept
bind shift_register shift_register_sva auto_sva_inst (
    .clk(clk),
    .data_in(data_in),
    .shift_in(shift_in),
    .load(load),
    .data_out(data_out)
);
