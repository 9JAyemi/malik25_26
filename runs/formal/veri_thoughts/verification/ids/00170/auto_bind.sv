// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_count, assert, property, posedge, h00, check_hold_when_disabled, disable, iff, initstate, past, check_up_wrap_from_ff, b0, hFF, check_down_wrap_from_zero, b1, check_up_single_step, h01, check_down_single_step, check_up_dual_step, h02, check_down_dual_step
bind counter counter_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .enable(enable),
    .count_dir(count_dir),
    .dual_count(dual_count),
    .count_out(count_out)
);
