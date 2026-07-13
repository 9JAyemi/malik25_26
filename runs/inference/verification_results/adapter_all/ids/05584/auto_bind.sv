// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_forces_clkout_low, assert, property, check_count_increments_when_not_max, disable, iff, past, d0, d1, check_count_wraps_when_max, check_zero_divisor_holds_state, check_zero_count_requires_max, check_zero_output_requires_max
bind ClockDivider ClockDivider_sva auto_sva_inst (
    .Divisor(Divisor),
    .clkOut(clkOut),
    .clk(clk),
    .rst(rst),
    .posedge(posedge),
    .b0(b0),
    .count_i(count_i)
);
