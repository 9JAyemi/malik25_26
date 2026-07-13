// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_enclk_low_at_posedge, assert, property, posedge, b0, check_enclk_matches_latched_enable, negedge, past, b1, check_en_low_clears_enclk, check_te_low_clears_enclk, check_both_high_sets_enclk, check_enclk_rise_cause, rose, check_enclk_fall_cause, fell, check_enclk_stays_high_when_enable_stays_high, check_enclk_stays_low_when_enable_stays_low
bind clock_gate clock_gate_sva auto_sva_inst (
    .clk(clk),
    .en(en),
    .te(te),
    .enclk(enclk)
);
