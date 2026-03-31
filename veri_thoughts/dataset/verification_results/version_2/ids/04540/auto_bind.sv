// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_stage0_sets_high, assert, property, posedge, disable, iff, b1, reset_reg, genvar, i, generate, for, RESET_SYNC_STAGES, begin, gen_shift_stage, check_shift_stage_update, past, end, endgenerate, if, gen_output_stage_checks, j, gen_output_stage, check_output_stage_update, check_output_release_latency, rose, b0
bind reset_synchronizer reset_synchronizer_sva auto_sva_inst (
    .reset_n_sync(reset_n_sync),
    .reset_n(reset_n),
    .clk(clk),
    .NUM_RESET_OUTPUT(NUM_RESET_OUTPUT)
);
