// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_out_hi_captures_prev_upper, assert, property, disable, iff, initstate, past, check_out_lo_captures_prev_lower, check_outputs_form_prev_input, check_stable_input_keeps_outputs_stable, stable, check_input_change_changes_output, changed, check_upper_change_updates_out_hi_only, check_lower_change_updates_out_lo_only, check_out_hi_change_implies_prev_upper_differs, check_out_lo_change_implies_prev_lower_differs, check_prev_stable_input_keeps_outputs_stable
bind split_16bit_input top_module_sva auto_sva_inst (
    .clk(clk),
    .in(in),
    .out_hi(out_hi),
    .out_lo(out_lo),
    .posedge(posedge)
);
