// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): counter, reset_sync_values, assert, property, posedge, d0, b1, on_read_loads_and_clears, disable, iff, d4, b0, on_write_loads_and_clears, read_has_priority_over_write, decrement_while_busy, past, d1, set_safe_when_count_one, hold_while_safe_idle, stay_unsafe_until_one, fall_requires_access, fell, rise_requires_reset_or_count1, rose, unsafe_never_zero_count, after_access_msb_high
bind hpdmc_banktimer hpdmc_banktimer_sva auto_sva_inst (
    .sys_clk(sys_clk),
    .sdram_rst(sdram_rst),
    .tim_cas(tim_cas),
    .tim_wr(tim_wr),
    .read(read),
    .write(write),
    .precharge_safe(precharge_safe)
);
