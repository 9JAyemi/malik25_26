// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_gray_counter_reset, assert, property, h00, check_shift_reg_reset, check_gray_counter_increment, disable, iff, b1, past, h01, check_shift_reg_load, check_shift_reg_shift, check_shift_reg_hold, check_counter_out_definition, check_shift_reg_out_definition, check_final_output_counter_path, check_final_output_shift_path
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
