// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_outputs_zero, assert, property, posedge, b0, b00, trans_00_to_01, disable, iff, b01, trans_01_to_10, b10, trans_10_to_11, b11, trans_11_to_00_overflow, b1, overflow_implies_zero, no_overflow_when_count_nonzero, overflow_single_cycle, post_reset_first_step, rose, wrap_two_step_progress
bind binary_counter binary_counter_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .count(count),
    .overflow(overflow)
);
