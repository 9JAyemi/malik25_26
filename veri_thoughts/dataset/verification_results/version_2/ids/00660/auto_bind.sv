// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_output_is_xor, assert, property, disable, iff, check_dff_samples_sr2, past, check_shift_sr2_advances, check_shift_sr1_advances, check_shift_sr0_captures_data, check_q_equals_sr2_xor_past, check_q_zero_if_sr2_stable, check_q_one_on_sr2_rise, rose, b1, check_q_one_on_sr2_fall, fell, check_shift_init_after_reset_release, b00, check_dff_zero_after_reset_release
bind top_module top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .data(data),
    .q(q),
    .shift_reg_out(shift_reg_out),
    .d_ff_out(d_ff_out),
    .posedge(posedge),
    .b0(b0)
);
