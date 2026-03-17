// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): comb_out_is_not, assert, property, disable, iff, shiftreg_updates_from_prev, past, q_captures_prev_complement_msb, q_equals_not_prev_shift2, q_is_not_data_3cycles_ago, shiftreg_msb_eq_data_2ago, reset_clears_shiftreg_next, b000, reset_clears_q_next, shiftreg_holds_zero_during_reset, q_holds_zero_during_reset
bind top_module top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .data(data),
    .q(q),
    .shift_reg(shift_reg),
    .complement(complement),
    .posedge(posedge),
    .b0(b0)
);
