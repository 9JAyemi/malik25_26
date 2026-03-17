// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_countfinished_definition, assert, property, posedge, disable, iff, check_reset_clears_countvalue, past, d0, check_reset_precedence_over_enable, check_hold_when_disabled, check_increment_when_enabled_ne_equal, d1, check_wrap_when_enabled_equal, check_changes_imply_enable_or_reset, check_countfinished_stable_when_inputs_stable, stable
bind Counter Counter_sva auto_sva_inst (
    .Clock(Clock),
    .Reset(Reset),
    .Enable(Enable),
    .CountTo(CountTo),
    .CountValue(CountValue),
    .CountFinished(CountFinished)
);
