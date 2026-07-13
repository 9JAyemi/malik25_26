// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_clkout, assert, property, check_clkout_low_during_reset, check_clkout_high_when_not_threshold, disable, iff, b1, check_clkout_low_when_threshold
bind ClockDivider ClockDivider_sva auto_sva_inst (
    .Divisor(Divisor),
    .clkOut(clkOut),
    .clk(clk),
    .rst(rst),
    .posedge(posedge),
    .b0(b0),
    .count_i(count_i)
);
