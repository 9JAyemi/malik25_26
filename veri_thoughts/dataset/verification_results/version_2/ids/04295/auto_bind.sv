// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reg1, reg2, reg3, reg4, shifted_reg1, shifted_reg2, shifted_reg3, check_reg1_captures_data_in, assert, property, posedge, b1, past, check_reg2_captures_reg1, check_reg3_captures_reg2, check_reg4_captures_reg3, check_reg4_four_cycle_delay, check_shifted_reg1_definition, check_shifted_reg2_definition, check_shifted_reg3_definition, check_data_out_equals_shifted_reg1, check_data_out_matches_delayed_input_shift
bind parallel_load_shift parallel_load_shift_sva auto_sva_inst (
    .clk(clk),
    .data_in(data_in),
    .shift_amount(shift_amount),
    .data_out(data_out)
);
