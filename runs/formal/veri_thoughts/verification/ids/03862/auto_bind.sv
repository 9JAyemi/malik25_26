// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_outputs, assert, property, posedge, b0, check_q_reg_captures_d, disable, iff, b1, past, check_q_count_accumulates_low_bits, check_q_count_holds_on_zero_addend, b000, check_q_count_wraps_on_overflow, b111, b001, check_final_output_mask_relation, check_final_output_upper_bits_zero
bind shift_register_and_counter shift_register_and_counter_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .d(d),
    .q_reg(q_reg),
    .q_count(q_count),
    .final_output(final_output)
);
