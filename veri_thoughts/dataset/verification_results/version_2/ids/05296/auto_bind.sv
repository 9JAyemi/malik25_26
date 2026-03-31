// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_sum_resets_to_zero, assert, property, posedge, sd0, check_sum_loads_addend_on_clear, disable, iff, past, check_sum_accumulates_on_enable, check_sum_holds_when_idle, check_clear_priority_over_enable, check_enable_out_follows_enable_high, check_enable_out_follows_enable_low
bind acc acc_sva auto_sva_inst (
    .clock(clock),
    .reset(reset),
    .clear(clear),
    .enable_in(enable_in),
    .enable_out(enable_out),
    .addend(addend),
    .sum(sum)
);
