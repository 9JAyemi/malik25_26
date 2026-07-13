// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_registers, assert, property, h00, check_counter_increments, disable, iff, b1, past, d1, check_counter_wraps, hFF, check_counter_output_function, check_shift_loads_data, check_shift_left, check_shift_hold, check_shift_output_function, check_final_output_selects_counter, check_final_output_selects_shift
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
    .gray_counter_out(gray_counter_out),
    .shift_reg(shift_reg),
    .posedge(posedge),
    .b0(b0)
);
