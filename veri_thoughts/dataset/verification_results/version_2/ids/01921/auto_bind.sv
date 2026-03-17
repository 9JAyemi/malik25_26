// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): PB_cnt_max, check_sync0_tracks_PB, assert, property, disable, iff, initstate, past, check_sync1_tracks_sync0, check_idle_definition, check_cntmax_definition, check_cnt_resets_when_idle_prev, d0, check_cnt_increments_when_active_prev, d1, check_state_changes_only_on_max, changed, check_state_changes_when_required, check_pb_down_definition, check_pb_up_definition, check_down_implies_not_up, check_up_implies_not_down, check_pb_down_single_cycle, check_pb_up_single_cycle
bind PushButton_Debouncer PushButton_Debouncer_sva auto_sva_inst (
    .clk(clk),
    .PB(PB),
    .PB_state(PB_state),
    .PB_down(PB_down),
    .PB_up(PB_up),
    .PB_sync_0(PB_sync_0),
    .PB_sync_1(PB_sync_1),
    .PB_cnt(PB_cnt),
    .PB_idle(PB_idle),
    .posedge(posedge)
);
