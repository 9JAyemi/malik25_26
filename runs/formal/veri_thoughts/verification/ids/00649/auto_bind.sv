// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): state, next, init_dly_cnt, IDLE, b000, START_CNT, b001, WAITFOR_CNT, b010, INIT_DDR, b011, b100, reset_state_to_idle, assert, property, posedge, reset_init_start_low, b0, reset_counter_zero, h00, check_state_updates_from_next, disable, iff, past, counter_increments, h01, next_from_idle_is_start, next_from_start_is_wait, next_from_wait_cnt_hit_is_initddr, h3c, next_from_wait_cnt_miss_is_wait, next_from_initddr_done_is_done, next_from_initddr_notdone_is_initddr, next_from_done_is_done, init_start_matches_next, state_transition_idle_to_start, state_transition_start_to_wait, state_transition_wait_hit_to_initddr, state_transition_initddr_done_to_done
bind ddr3_init_sm ddr3_init_sm_sva auto_sva_inst (
    .rst(rst),
    .clk(clk),
    .init_done(init_done),
    .init_start(init_start),
    .INIT_DONE(init_done)
);
