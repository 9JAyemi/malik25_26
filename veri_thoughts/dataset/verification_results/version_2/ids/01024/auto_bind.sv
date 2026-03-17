// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_forces_outputs_zero, assert, property, hold_zero_while_reset_held, past, stable_during_reset, stable, or_out_zero_after_reset_release, q_captures_d, disable, iff, or_out_matches_prev_q_or, or_out_rise_implies_prev_q_nonzero, rose, or_out_fall_implies_prev_q_zero, fell, or_out_one_if_prev_q_nonzero, b1, or_out_zero_if_prev_q_zero
bind dff_with_reset_and_or dff_with_reset_and_or_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .d(d),
    .q(q),
    .or_out(or_out),
    .negedge(negedge),
    .b0(b0)
);
