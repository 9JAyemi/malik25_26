// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_leds_mirror_count, assert, property, posedge, disable, iff, check_reset_clears_count_next, d0, check_reset_held_keeps_zero, past, check_reset_clears_leds_next, check_increment_each_cycle_no_reset, d1, check_two_cycle_stride_no_reset, d2, check_wrap_from_F_to_0, hF, h0, check_no_stall_when_no_reset, check_first_value_after_reset_is_1, check_leds_increment_no_reset
bind SyncCounter SyncCounter_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .count(count),
    .leds(leds)
);
