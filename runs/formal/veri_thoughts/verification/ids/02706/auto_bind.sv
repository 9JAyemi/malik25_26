// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): CLK, check_a_gt_b_drives_a_and_sel00, assert, property, posedge, b00, check_b_gt_a_drives_b_and_sel01, b01, check_equal_drives_a_and_sel_passthrough, check_result_is_either_a_or_b, check_sel_msb_one_only_when_equal, b1, check_not_equal_forces_sel_msb_zero, b0, check_result_b_implies_b_gt_a_and_sel01, check_result_a_implies_a_ge_b, check_select_irrelevant_when_not_equal, stable, check_select_passthrough_when_equal_changes
bind magnitude_comparator_selector magnitude_comparator_selector_sva auto_sva_inst (
    .a(a),
    .b(b),
    .select(select),
    .comparison_result(comparison_result),
    .input_selected(input_selected)
);
