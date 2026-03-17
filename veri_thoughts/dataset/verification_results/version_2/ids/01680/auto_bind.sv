// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): shift_reg, reset_clears_shift_reg, assert, property, posedge, b000, load_writes_shift_reg, disable, iff, past, shift_when_no_load, b0, zero_sticky_when_shifting, flush_after_three_shifts, out_is_definition, out_zero_when_any_input_zero, out_follows_shiftreg0_when_inputs_one, b1, out_reflects_loaded_lsb, out_reflects_shifted_lsb
bind shift_and shift_and_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .load(load),
    .load_data(load_data),
    .and_input(and_input),
    .out(out)
);
