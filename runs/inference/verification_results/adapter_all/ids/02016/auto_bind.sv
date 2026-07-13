// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): counter, reset_values, assert, property, posedge, d0, b1, read_sets_counter_and_clears_safe, disable, iff, d4, b0, write_sets_counter_and_clears_safe, hold_counter_without_rw, past, hold_safe_without_rw, counter_decrements_without_rw, d1, safe_clears_without_rw, counter_nonzero_without_rw, safe_low_without_rw, counter_range_without_rw, inside, d7
bind hpdmc_banktimer hpdmc_banktimer_sva auto_sva_inst (
    .sys_clk(sys_clk),
    .sdram_rst(sdram_rst),
    .tim_cas(tim_cas),
    .tim_wr(tim_wr),
    .read(read),
    .write(write),
    .precharge_safe(precharge_safe)
);
