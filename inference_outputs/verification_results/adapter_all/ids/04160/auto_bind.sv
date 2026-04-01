// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_outputs, assert, property, h00, check_reset_clears_select_path, check_reset_clears_counter_path, check_counter_matches_gray_counter, disable, iff, check_shift_reg_matches_gray_shift_reg, check_final_output_selects_gray_path, check_load_captures_shift_reg, past, check_shift_moves_shift_reg, check_hold_shift_reg, check_gray_counter_increments, b1, h01
bind gray_shift_register gray_shift_register_sva auto_sva_inst (
    .CLK(CLK),
    .RST(RST),
    .data_in(data_in),
    .shift(shift),
    .load(load),
    .select(select),
    .shift_reg_out(shift_reg_out),
    .counter_out(counter_out),
    .final_output(final_output),
    .posedge(posedge),
    .gray_counter_out(gray_counter_out),
    .shift_reg(shift_reg),
    .b0(b0)
);
