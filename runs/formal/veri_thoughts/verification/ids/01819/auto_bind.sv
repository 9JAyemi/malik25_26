// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_values, assert, property, posedge, d0, b0, b1, por_req_clears_on_input, disable, iff, por_req_only_falls_on_input, fell, por_req_rise_only_on_reset, rose, control_tag_set_on_input, control_tag_clear_on_dequeue_only, control_tag_priority_over_dequeue, control_tag_fall_requires_dequeue, control_tag_stable_when_idle, stable, capture_data_on_valid, valid_sets_on_valid_no_dequeue, valid_cleared_on_dequeue, valid_rise_requires_valid_not_dequeue, valid_fall_requires_dequeue, valid_stable_when_idle, data_ecc_tag_stable_without_valid, dequeue_flag_set_on_input, dequeue_flag_only_rises_on_input, dequeue_flag_never_falls_without_reset, error_set_on_input, error_only_rises_on_error, error_never_falls_without_reset, outputs_stable_when_fully_idle
bind data_buffer data_buffer_sva auto_sva_inst (
    .data_in(data_in),
    .ecc_in(ecc_in),
    .tag_in(tag_in),
    .valid_in(valid_in),
    .control_tag_in(control_tag_in),
    .error_in(error_in),
    .dequeue_in(dequeue_in),
    .por_req_in(por_req_in),
    .clk(clk),
    .reset(reset),
    .data_out(data_out),
    .ecc_out(ecc_out),
    .tag_out(tag_out),
    .valid_out(valid_out),
    .control_tag_out(control_tag_out),
    .error_out(error_out),
    .dequeue_out(dequeue_out),
    .por_req_out(por_req_out)
);
