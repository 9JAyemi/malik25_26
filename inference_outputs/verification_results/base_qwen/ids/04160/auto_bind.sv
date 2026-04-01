// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): shift_reg_increment, assert, property, disable, iff, gray_counter_increment, shift_reg_load, b1, shift_reg_shift, final_output_select, counter_output_comb, shift_reg_output_comb
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
    .shift_reg(shift_reg),
    .gray_counter_out(gray_counter_out),
    .b0(b0)
);
