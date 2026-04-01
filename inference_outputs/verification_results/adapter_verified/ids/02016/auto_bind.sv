// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): counter, check_reset_clears_state, assert, property, posedge, d0, b1, check_read_sets_counter_and_clears_safe, disable, iff, d4, b0, check_write_zero_sets_counter_and_clears_safe, d3, check_write_one_sets_counter_and_clears_safe, d1, d2, check_write_two_sets_counter_and_clears_safe, check_write_three_sets_counter_and_clears_safe, check_counter_one_sets_safe, check_counter_not_one_keeps_safe_low, check_counter_decrements_when_safe_low, past, check_counter_holds_when_safe_high
bind hpdmc_banktimer hpdmc_banktimer_sva auto_sva_inst (
    .sys_clk(sys_clk),
    .sdram_rst(sdram_rst),
    .tim_cas(tim_cas),
    .tim_wr(tim_wr),
    .read(read),
    .write(write),
    .precharge_safe(precharge_safe)
);
