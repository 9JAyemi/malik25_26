// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reg1, reg2, reg3, reg4, check_reset_clears_state, assert, property, posedge, b0000, check_load_captures_reg1, disable, iff, past, check_reg1_holds_without_load, check_reg2_shifts_reg1, b1, check_reg3_shifts_reg2, check_reg4_shifts_reg3, check_data_out_matches_reg4, check_load_reaches_output_after_four_cycles
bind shift_register shift_register_assertions auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .load(load),
    .data_in(data_in),
    .data_out(data_out)
);
