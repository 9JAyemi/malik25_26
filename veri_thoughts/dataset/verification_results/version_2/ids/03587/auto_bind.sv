// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): delay_reg, error, error_filtered, error_integrated, error_integrated_next, error_filtered_next, phase_detector_out, delay_line_out, out_clk_reg, out_clk_next, check_delay_reg_captures_delay, assert, property, posedge, b1, past, check_error_captures_phase_detector, check_error_filtered_updates, check_error_integrated_updates, check_out_clk_reg_updates, check_out_clk_matches_out_clk_reg_lsb, check_delay_line_out_final_assignment, h01, check_phase_detector_out_xor, check_error_filtered_next_computation, check_error_integrated_next_computation, check_out_clk_next_final_assignment
bind DLL DLL_sva auto_sva_inst (
    .ref_clk(ref_clk),
    .feedback_clk(feedback_clk),
    .delay(delay),
    .out_clk(out_clk)
);
