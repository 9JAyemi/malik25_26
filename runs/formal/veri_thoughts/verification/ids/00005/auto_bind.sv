// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): count, curr, check_done_zero_when_count_nonzero, assert, property, posedge, disable, iff, initstate, b0000, b00, check_done_matches_curr_when_count_zero, check_globalreset_loads_state, b1000, check_reset_loads_state, check_zero_count_reloads_state, check_valid_newresult_decrements_count, past, b0001, check_valid_newresult_updates_curr, check_idle_holds_count, check_idle_holds_curr, check_terminal_result_drives_done
bind resultcounter resultcounter_sva auto_sva_inst (
    .resultID(resultID),
    .newresult(newresult),
    .done(done),
    .reset(reset),
    .globalreset(globalreset),
    .clk(clk)
);
