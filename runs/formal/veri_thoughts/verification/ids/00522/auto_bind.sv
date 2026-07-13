// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_counter_clears_after_reset, assert, property, posedge, disable, iff, initstate, b000, check_counter_counts_up, past, b001, check_counter_counts_down, check_comparator_gt_code, check_comparator_lt_code, check_comparator_eq_code, check_final_selects_a, check_final_selects_b, check_final_default_path, check_top_output_when_a_gt_b, check_top_output_when_a_lt_b, check_top_output_when_a_eq_b
bind final_module top_module_assertions auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .A(A),
    .B(B),
    .up_down(up_down),
    .final_output(final_output),
    .comparator_output(comparator_output),
    .up_down_output(up_down_output),
    .b01(b01),
    .b10(b10),
    .b00(b00)
);
