// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_definition, assert, property, check_counter_next_zero, b1, check_counter_next_zero_when_reset_low, check_counter_wrap_from_3_to_0, check_clk_out_forced_low, b0, check_clk_out_stable_when_reset_high, past, check_clk_out_low_after_prev_reset_low, check_reset_low_when_counter_zero, check_reset_single_cycle_pulse, check_reset_stays_low
bind clk32to40 clk32to40_sva auto_sva_inst (
    .CLK_IN1(CLK_IN1),
    .CLK_OUT(CLK_OUT),
    .counter(counter),
    .reset(reset),
    .posedge(posedge),
    .b11(b11),
    .b00(b00)
);
