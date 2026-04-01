// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): counter, check_reset_clears_state, assert, property, posedge, d0, b1, check_read_sets_counter_and_clears_precharge, disable, iff, d4, b0, check_write_sets_counter_from_tim_wr_and_clears_precharge, check_idle_holds_counter, past, check_idle_holds_precharge_safe, check_counter_decrements_when_precharge_low, d1, check_counter_holds_when_precharge_high, check_precharge_safe_set_on_counter_one
bind hpdmc_banktimer hpdmc_banktimer_sva auto_sva_inst (
    .sys_clk(sys_clk),
    .sdram_rst(sdram_rst),
    .tim_cas(tim_cas),
    .tim_wr(tim_wr),
    .read(read),
    .write(write),
    .precharge_safe(precharge_safe)
);
