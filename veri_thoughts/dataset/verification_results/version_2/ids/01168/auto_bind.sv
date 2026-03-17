// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): data_in_d1, check_clk1_prev_reset_low_zero_now, assert, property, posedge, past, b0, check_clk1_reset_low_next_zero, check_clk1_consecutive_reset_low_zero, check_clk1_reset_release_zero_sample, disable, iff, rose, check_clk2_prev_reset_low_zero_now, check_clk2_reset_low_next_zero, check_clk2_consecutive_reset_low_zero, check_clk2_reset_release_zero_sample
bind kernel_clock_0_bit_pipe kernel_clock_0_bit_pipe_sva auto_sva_inst (
    .clk1(clk1),
    .clk2(clk2),
    .data_in(data_in),
    .reset_clk1_n(reset_clk1_n),
    .reset_clk2_n(reset_clk2_n),
    .data_out(data_out)
);
