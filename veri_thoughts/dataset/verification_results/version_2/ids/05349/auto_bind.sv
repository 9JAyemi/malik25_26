// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_state_clears_after_reset, assert, property, disable, iff, initstate, past, b0000, b00000000, check_sum_clears_after_reset, check_count_increments, b0001, check_output1_captures_data_in1, check_output2_captures_data_in2, check_sum_uses_output1_when_select_low, check_sum_uses_output2_when_select_high, b1
bind mux_counter mux_counter_sva auto_sva_inst (
    .clk(clk),
    .data_in1(data_in1),
    .data_in2(data_in2),
    .select(select),
    .reset(reset),
    .sum_out(sum_out),
    .count(count),
    .output1(output1),
    .output2(output2),
    .posedge(posedge),
    .b0(b0)
);
