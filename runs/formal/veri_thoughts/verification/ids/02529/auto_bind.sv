// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): CLK, add_low_nibble_matches_full_add, assert, property, posedge, b0, sub_low_nibble_matches_full_sub, s_independent_of_DI_changes, stable, s_independent_of_selectorB_changes, s_independent_of_Q_upper_bits, s_independent_of_Qreg_upper_bits, s_passthrough_when_Q_zero, h00, s_zero_when_both_low_nibbles_zero, h0, add_low_nibble_depends_only_on_low_nibbles, hF, sub_low_nibble_depends_only_on_low_nibbles
bind add_sub_carry_out add_sub_carry_out_sva auto_sva_inst (
    .S(S),
    .Q_reg(Q_reg),
    .Q(Q),
    .FSM_exp_operation_A_S(FSM_exp_operation_A_S),
    .FSM_selector_B(FSM_selector_B),
    .DI(DI)
);
