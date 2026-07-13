// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_q_next, assert, property, d0, hold_zero_while_reset, past, q_change_is_zero_or_plus1, disable, iff, changed, d1, increment_implies_prev_slowena_low, b0, no_back_to_back_increments, no_increment_when_slowena_high, slowena_high_two_cycles_stabilizes_q, zero_to_nonzero_becomes_one, slowena_fall_causes_increment_next, post_reset_deassert_with_slowena_high_holds_q
bind decade_counter decade_counter_sva auto_sva_inst (
    .clk(clk),
    .slowena(slowena),
    .reset(reset),
    .q(q),
    .posedge(posedge)
);
