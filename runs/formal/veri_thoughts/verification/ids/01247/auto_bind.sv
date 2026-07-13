// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_q, assert, property, reset_sets_state_idle, q_matches_count_reg, hold_when_disabled, disable, iff, past, zero_on_enable_from_idle, inc_by_one_in_count, d1, inc_by_two_in_count_by_two, d2, state_idle_to_count, state_count_to_cbt, state_cbt_to_count, state_to_idle_when_disabled, inside, next_state_idle_when_disabled, next_state_idle_enable_to_count, next_state_count_disabled_to_idle, next_state_count_enable_to_cbt, next_state_cbt_disabled_to_idle, next_state_cbt_enable_to_count, state_follows_next_state
bind up_counter up_counter_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .ena(ena),
    .q(q),
    .state(state),
    .next_state(next_state),
    .count_reg(count_reg),
    .IDLE(IDLE),
    .b00(b00),
    .COUNT(COUNT),
    .b01(b01),
    .COUNT_BY_TWO(COUNT_BY_TWO),
    .b10(b10),
    .posedge(posedge),
    .d0(d0)
);
