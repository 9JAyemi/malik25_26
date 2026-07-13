// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): count_reg1, count_reg2, check_sync_reset_clears_count, assert, property, posedge, disable, iff, d0, check_load_captures_L, past, check_free_run_increments_from_count_reg1, d1, check_reset_overrides_load, check_async_reset_clears_pipe_regs, check_async_reset_recovery_counts_one
bind sync_load_counter sync_load_counter_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .load(load),
    .L(L),
    .areset(areset),
    .count(count)
);
