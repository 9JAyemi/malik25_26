// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reg_out_equals_shifted_in, assert, property, disable, iff, check_reg_out_lsb_is_zero, check_reg_out_upper_bits_map, check_out_is_xor_of_inputs, check_shift_reg_captures_reg_out_next_cycle, b1, past, check_reset_clears_shift_reg_next_cycle, h00, check_out_equals_in_one_cycle_after_reset, check_shift_reg_stays_zero_while_reset, check_shift_reg_captures_shifted_in_next_cycle, check_pipeline_out_uses_prev_shifted_in, check_reg_out_stable_when_in_stable, stable
bind shift_register shift_register_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .in(in),
    .out(out),
    .reg_out(reg_out),
    .shift_reg(shift_reg),
    .posedge(posedge),
    .b0(b0)
);
