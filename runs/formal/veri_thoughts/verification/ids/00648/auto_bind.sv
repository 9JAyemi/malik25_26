// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_on_next, assert, property, posedge, disable, iff, past, h00, check_zero_during_reset, check_load_updates_count, check_increment_updates_count, d1, check_stable_when_no_action, check_increment_wraparound, hFF, check_load_overrides_increment, check_change_implies_cause, check_enable_without_increment_no_change, check_increment_without_enable_no_change
bind counter counter_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .enable(enable),
    .load(load),
    .increment(increment),
    .data_in(data_in),
    .count(count)
);
