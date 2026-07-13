// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_clears_outputs, assert, property, h00, h0, check_q_low_nibble_zero, disable, iff, check_ena_matches_encoder, b00, check_count_0_to_1, h10, check_count_1_to_2, h20, check_count_2_to_3, h30, check_count_3_to_4, h40, check_count_4_to_5, h50, check_count_5_to_6, h60, check_count_6_to_7, h70, check_count_7_to_8, h80, check_count_8_to_9, h90, check_count_9_to_0, check_invalid_digit_recovers_to_zero, d9
bind bcd_counter top_module_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .ena(ena),
    .q(q),
    .posedge(posedge)
);
