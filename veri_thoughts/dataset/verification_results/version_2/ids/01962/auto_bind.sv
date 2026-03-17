// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): decprep_low_when_scryptin_high, assert, property, posedge, b0, decprep_high_when_scryptin_low, negedge, b1, scryptin_low_on_decprep_rise, scryptin_high_on_decprep_fall, result_flag_matches_prep_on_scryptin_rise, d0, result_flag_matches_prep_on_scryptin_fall, result_flag_rise_requires_positive_prep, result_flag_fall_requires_zero_prep, inc_dec_conditions_mutex, d3, no_update_when_doWork_high
bind react react_sva auto_sva_inst (
    .pipelineReady(pipelineReady),
    .scheduleTask(scheduleTask),
    .workCounter(workCounter),
    .scryptResultAvailableIn(scryptResultAvailableIn),
    .doWork(doWork),
    .preparing(preparing),
    .decreasePrepare(decreasePrepare),
    .scryptResultAvailable(scryptResultAvailable)
);
