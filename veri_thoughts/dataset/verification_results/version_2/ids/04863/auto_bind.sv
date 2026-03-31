// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_q, assert, property, check_capture_low_byte_sum, disable, iff, past, check_post_reset_q_zero, check_same_low_bytes_hold_q, check_zero_left_operand_passthrough, check_zero_right_operand_passthrough, check_overflow_wraps_to_zero, b0, h100
bind reverse_byte_order adder_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .in1(in1),
    .in2(in2),
    .q(q),
    .negedge(negedge),
    .h00(h00)
);
