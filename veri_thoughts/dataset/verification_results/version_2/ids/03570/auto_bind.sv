// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): pipeline_reg1, pipeline_reg2, pipeline_reg3, check_reset_clears_state, assert, property, posedge, b0, check_post_reset_zero_state, disable, iff, past, check_first_active_cycle_after_reset, fell, b1, check_pipeline_reg1_captures_out, check_pipeline_reg2_captures_reg1, check_pipeline_reg3_captures_reg2, check_out_updates_from_pipeline_reg3, d1, check_pipeline_reg2_two_cycle_delay, check_pipeline_reg3_three_cycle_delay, check_out_four_cycle_recurrence
bind counter counter_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .out(out)
);
