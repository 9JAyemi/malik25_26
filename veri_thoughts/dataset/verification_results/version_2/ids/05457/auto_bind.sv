// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_serial_out, assert, property, check_reset_clears_final_output, check_shift_left_update, disable, iff, past, check_shift_right_update, check_final_output_equal_case, b1, check_final_output_greater_case, check_final_output_less_case
bind shift_comp shift_comp_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .serial_in(serial_in),
    .shift_direction(shift_direction),
    .serial_out(serial_out),
    .final_output(final_output),
    .posedge(posedge),
    .b0(b0),
    .b1010(b1010)
);
