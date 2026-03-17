// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): shift_reg, check_dout_equals_shift_reg, assert, property, posedge, reset_clears_next_cycle, d0, hold_zero_while_reset, past, deassert_reset_zero_now, fell, reset_overrides_load, load_captures_din_next, disable, iff, rotate_vector_when_no_load, rotate_bit3_from_prev_bit2, rotate_bit2_from_prev_bit1, rotate_bit1_from_prev_bit0, rotate_bit0_from_prev_bit3, four_rotations_return_to_original
bind shift_register shift_register_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .load(load),
    .din(din),
    .dout(dout)
);
