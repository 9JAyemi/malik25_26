// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_out_zero_after_reset_fall, assert, property, posedge, disable, iff, fell, d0, check_zero_persists_one_cycle_if_no_enable_after_reset, check_out_zero_immediately_after_reset_fall_even_if_enable, check_prev_enable1_next_out_plus_one_or_zero, past, d1, check_prev_enable0_next_out_same_or_zero, check_prev_enable1_wrap_from_F_to_0, hF, check_prev_enable0_nonzero_implies_stable, check_prev_enable1_nonzero_implies_plus_one, check_prev_zero_holds_when_enable0
bind counter counter_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .enable(enable),
    .out(out)
);
