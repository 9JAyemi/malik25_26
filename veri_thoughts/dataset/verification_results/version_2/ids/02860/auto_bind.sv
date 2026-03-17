// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears, assert, property, posedge, b0000, reset_overrides_load, load_writes_next, disable, iff, past, shift_next_value, b0, shift_lsb_zero, shift_bit1_from_bit0, shift_bit2_from_bit1, shift_bit3_from_bit2, four_shifts_zero, load_then_shift_moves_loaded_bit2_to_msb
bind shift_register shift_register_sva auto_sva_inst (
    .clk(clk),
    .load(load),
    .data_in(data_in),
    .reset(reset),
    .data_out(data_out)
);
