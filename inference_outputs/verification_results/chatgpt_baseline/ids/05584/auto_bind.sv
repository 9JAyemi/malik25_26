// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_clkout_matches_internal, assert, property, disable, iff, check_count_zero_after_reset_release, fell, d0, check_clkout_reg_low_after_reset_release, check_count_wraps_at_terminal_count, check_count_increments_when_not_terminal, past, d1, check_clkout_reg_toggles_at_terminal_count, check_clkout_reg_holds_when_not_terminal
bind ClockDivider ClockDivider_sva auto_sva_inst (
    .Divisor(Divisor),
    .clkOut(clkOut),
    .clk(clk),
    .rst(rst),
    .count_i(count_i),
    .clkOut_i(clkOut_i),
    .posedge(posedge),
    .b0(b0)
);
