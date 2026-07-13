// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_increment_request_to_increment_outputs, assert, property, posedge, disable, iff, check_load_only_request_to_load_outputs, check_no_request_to_read_outputs, check_increment_priority_over_load, check_request_sets_writeorread, check_addone_implies_writeorread, check_outputs_idle_after_reset_release, fell
bind OverallController OverallController_sva auto_sva_inst (
    .Clock(Clock),
    .IncrementData(IncrementData),
    .LoadData(LoadData),
    .Reset(Reset),
    .AddOne(AddOne),
    .WriteOrRead(WriteOrRead)
);
