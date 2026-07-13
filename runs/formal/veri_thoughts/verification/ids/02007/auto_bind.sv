// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): shift_reg, mux_sel, check_reset_state_regs, assert, property, posedge, b0, check_reset_q_eq_seed, check_reset_fall_regs_zero, fell, check_reset_fall_q_zero, h00, check_shift_reg_update, disable, iff, past, check_mux_sel_update, check_q_update_from_taps, check_zero_state_absorbing, check_reset_state_stable, b1, stable
bind prng prng_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .seed(seed),
    .q(q)
);
