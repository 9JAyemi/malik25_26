// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): load_updates_out, assert, property, posedge, past, load_has_priority_over_shift, shift_updates_out_when_no_load, b0, hold_when_no_op, shift_zero_fill_lsb, shift_msb_from_prev_bit2, shift_bit2_from_prev_bit1, shift_bit1_from_prev_bit0, double_left_shift_over_two_cycles, b00
bind shift_register shift_register_sva auto_sva_inst (
    .data_in(data_in),
    .shift(shift),
    .load(load),
    .clk(clk),
    .out(out)
);
