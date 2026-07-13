// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_next_indicator_passthrough, assert, property, disable, iff, check_next_indicator_passthrough_during_reset, check_next_indicator_rise_match, rose, check_next_indicator_fall_match, fell, check_no_spurious_rise_on_next_indicator, check_no_spurious_fall_on_next_indicator, check_stable_indicator_implies_stable_next, stable, check_stable_next_implies_stable_indicator, check_dout_equals_din_during_reset
bind data_whiting data_whiting_sva auto_sva_inst (
    .clk(clk),
    .reset_n(reset_n),
    .din(din),
    .indicator(indicator),
    .dout(dout),
    .next_indicator(next_indicator),
    .posedge(posedge)
);
