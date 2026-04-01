// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): function, automatic, gray2bin, g, endfunction, check_reset_clears_outputs, assert, property, h00, check_final_output_selects_shift, disable, iff, check_final_output_selects_counter, check_counter_increments, past, d1, check_counter_gray_step, onehot, check_shift_reg_loads_data, check_shift_reg_shifts_left, check_shift_reg_holds_value
bind gray_shift_register gray_shift_register_assertions auto_sva_inst (
    .CLK(CLK),
    .RST(RST),
    .data_in(data_in),
    .shift(shift),
    .load(load),
    .select(select),
    .shift_reg_out(shift_reg_out),
    .counter_out(counter_out),
    .final_output(final_output),
    .begin(begin),
    .end(end),
    .posedge(posedge)
);
