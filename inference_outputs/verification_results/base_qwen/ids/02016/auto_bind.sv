// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_counter, assert, property, posedge, disable, iff, counter, d0, reset_precharge_safe, b1, read_counter_set, d4, read_precharge_safe_set, b0, write_counter_set, write_precharge_safe_set, decrement_counter, d1, set_precharge_safe, read_write_counter_stable, read_write_precharge_safe_stable, tim_cas_counter_stable, tim_cas_precharge_safe_stable
bind hpdmc_banktimer hpdmc_banktimer_sva auto_sva_inst (
    .sys_clk(sys_clk),
    .sdram_rst(sdram_rst),
    .tim_cas(tim_cas),
    .tim_wr(tim_wr),
    .read(read),
    .write(write),
    .precharge_safe(precharge_safe)
);
