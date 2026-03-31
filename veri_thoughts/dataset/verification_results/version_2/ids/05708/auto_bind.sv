// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_drives_ready_low, assert, property, posedge, b0, check_reset_clears_process_output, d0, check_nonzero_output_change_implies_ready, disable, iff, initstate, changed, b1, check_prefixed_output_uses_prior_input, past, check_msb_low_nonzero_output_is_one, d1, check_output_one_requires_prior_ready_downstream, check_zero_output_change_requires_reset, check_ready_low_holds_process_output, stable, check_ready_rise_has_nonzero_output, rose
bind myModule myModule_sva auto_sva_inst (
    .CLK(CLK),
    .ready_downstream(ready_downstream),
    .ready(ready),
    .reset(reset),
    .process_input(process_input),
    .process_output(process_output)
);
